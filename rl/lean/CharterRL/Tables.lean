import Server.ArenaPlay
import Server.LawLibrary
import Server.Rules
import Evolved.Pool
import CharterRL.Layout

/-!
# What the environment knows about a game before it starts

`Tables` holds what never changes for a game, worked out once when the library loads. Values made while a module
loads are never counted or copied afterwards, so every thread can read them at no cost. `Settings` holds the named
switches. `Opponent` is a named way to play from the arena's pool.
-/

namespace CharterRL
open Charter CharterServer CharterServer.Bots

/-! ## Laws, by what they do -/

mutual
  /-- This number reads what a seat declared. -/
  def readsDeclaredE : Expr → Bool
    | .declared _ _ => true
    | .add a b | .sub a b | .mul a b | .min a b | .max a b | .divBy a b => readsDeclaredE a || readsDeclaredE b
    | .div a _ => readsDeclaredE a
    | .totalOver c a | .mostOver c a | .leastOver c a => readsDeclaredC c || readsDeclaredE a
    | _ => false

  /-- This test reads what a seat declared. -/
  def readsDeclaredC : Cond → Bool
    | .lt a b | .le a b | .eq a b => readsDeclaredE a || readsDeclaredE b
    | .and a b | .or a b => readsDeclaredC a || readsDeclaredC b
    | .not c => readsDeclaredC c
    | _ => false
end

mutual
  /-- This effect reads what a seat declared. -/
  def readsDeclaredF : Effect → Bool
    | .transfer _ _ _ amount => readsDeclaredE amount
    | .movePiece .. => false
    | .forEach c body | .when c body => readsDeclaredC c || readsDeclaredAll body

  /-- One of these effects reads what a seat declared. -/
  def readsDeclaredAll : List Effect → Bool
    | [] => false
    | e :: es => readsDeclaredF e || readsDeclaredAll es
end

/-- This law reads what a seat declared. -/
def Law.readsDeclared (L : Law) : Bool :=
  L.clauses.any fun c => readsDeclaredAll c.effects

/-- A law's columns of `lawShape`, in that order. -/
structure LawCounts where
  transfers : Nat := 0
  moves : Nat := 0
  forEach : Nat := 0
  when_ : Nat := 0
  from_ : Array Nat := #[0, 0, 0, 0]
  to_ : Array Nat := #[0, 0, 0, 0]

private def partyIdx : Party → Nat
  | .actor => 0 | .each => 1 | .treasury => 2 | .bank => 3

mutual
  private def countEffect (c : LawCounts) : Effect → LawCounts
    | .transfer src dst _ _ =>
      { c with transfers := c.transfers + 1, from_ := c.from_.modify (partyIdx src) (· + 1), to_ := c.to_.modify (partyIdx dst) (· + 1) }
    | .movePiece src dst _ =>
      { c with moves := c.moves + 1, from_ := c.from_.modify (partyIdx src) (· + 1), to_ := c.to_.modify (partyIdx dst) (· + 1) }
    | .forEach _ body => countEffects { c with forEach := c.forEach + 1 } body
    | .when _ body => countEffects { c with when_ := c.when_ + 1 } body

  private def countEffects (c : LawCounts) : List Effect → LawCounts
    | [] => c
    | e :: es => countEffects (countEffect c e) es
end

/-- The numbers of `lawShape` for this law, scaled. -/
def Law.shape (L : Law) : Array Float :=
  let clause (test : Clause → Bool) : Float := Float.ofNat (L.clauses.filter test).length
  let c := L.clauses.foldl (fun c x => countEffects c x.effects) ({} : LawCounts)
  let scale (n : Nat) : Float := Float.ofNat n / 4
  #[ clause (fun | .onHarvest _ => true | _ => false)
   , clause (fun | .onBuild .. => true | _ => false)
   , clause (fun | .onRoundEnd _ => true | _ => false)
   , clause (fun | .onRoll _ => true | _ => false)
   , clause (fun | .now _ => true | _ => false)
   , clause (fun | .setCost .. => true | _ => false)
   , clause (fun | .setPoints .. => true | _ => false)
   , clause (fun | .setBankRate _ => true | _ => false)
   , clause (fun | .setWorth .. => true | _ => false)
   , clause (fun | .newPiece _ => true | _ => false)
   , clause (fun | .endGame => true | _ => false)
   , clause (fun | .repeal _ => true | _ => false)
   , scale c.transfers, scale c.moves, scale c.forEach, scale c.when_ ]
  ++ (c.from_ ++ c.to_).map scale ++ #[Float.ofNat L.size / 128]

/-! ## A game's tables -/

instance : Inhabited Region := ⟨{ res := "", number := 0, spots := [] }⟩


/-- What never changes for a game. -/
structure Tables where
  id : String
  G : GameDef
  minSeats : Nat
  maxSeats : Nat
  board : Board G
  /-- Each spot's place on the board, from -1 to 1. -/
  spotXY : Array (Float × Float)
  /-- Each link's ends. -/
  links : Array (Nat × Nat)
  /-- The links that start at a spot, as the other end and the link's place. -/
  linkFrom : Array (List (Nat × Nat))
  /-- The laws this game's environment can put to a vote. -/
  library : Array Law
  /-- Some law can read a declared number, so declaring can matter. -/
  declares : Bool

/-- The Island's tables. Only a default for `Inhabited`; nothing plays it by this name. -/
instance : Inhabited Tables where
  default :=
    let G := islandSpec.G
    { id := "", G, minSeats := 2, maxSeats := 6, board := Board.of G, spotXY := #[], links := #[]
      linkFrom := #[], library := #[], declares := false }

/-- A game's own laws and library decide whether declaring is offered. -/
def declaresIn (G : GameDef) (library : Array Law) : Bool :=
  G.foundingLaws.any Law.readsDeclared || library.any Law.readsDeclared

/-- The tables of a game, from its definition and layout. -/
def Tables.make (id : String) (G : GameDef) (minSeats maxSeats : Nat) (library : Array Law)
    (spotXY : Array (Float × Float)) : Tables :=
  let links := G.map.links.toArray
  let high := G.map.spotCount
  let linkFrom := links.foldl (fun (acc : Nat × Array (List (Nat × Nat))) l =>
      (acc.1 + 1, acc.2.modify l.1 (· ++ [(l.2, acc.1)]))) (0, Array.replicate high []) |>.2
  { id, G, minSeats, maxSeats, board := Board.of G, spotXY, links, linkFrom, library
    declares := declaresIn G library }

/-- Spots' places on the board, from -1 to 1. -/
def normalised (points : List (Float × Float)) : Array (Float × Float) :=
  let top := points.foldl (fun m p => max m (max p.1.abs p.2.abs)) 0
  let top := if top == 0 then 1 else top
  points.toArray.map fun p => (p.1 / top, p.2 / top)

/-- The laws of a game's list that read correctly. -/
def libraryOf (spec : GameSpec) : Array Law :=
  let names := spec.G.resources.map (·.name)
  ((PreviewCheck.lawsFor spec).filterMap fun text =>
    match Rules.parseProposal text names with
    | .ok (.law L) => some L
    | _ => none).toArray

def Tables.ofSpec (spec : GameSpec) : Tables :=
  Tables.make spec.id spec.G spec.minSeats spec.maxSeats (libraryOf spec)
    (normalised (spec.layout.spots.map (·.toPixel 1.0)))

/-- Every game's tables. -/
def allTables : Array Tables := gameSpecs.toArray.map Tables.ofSpec

/-- The training games and the held-out games, in `rl/games.json`. -/
def tablesOf? (id : String) : Option Tables := allTables.find? (·.id == id)

/-- Why this game does not fit the layout, if it does not. -/
def Tables.problems (T : Tables) : List String :=
  let G := T.G
  let linkKinds := (G.pieces.filter fun d => match d.placement with | .link => true | _ => false).length
  (if G.resources.length ≤ maxRes then [] else [s!"{G.resources.length} resources, and the limit is {maxRes}"]) ++
  (if linkKinds ≤ maxLinkKinds then [] else [s!"{linkKinds} kinds of link piece, and the limit is {maxLinkKinds}"]) ++
  (if G.pieces.length - linkKinds ≤ maxSpotKinds then [] else [s!"{G.pieces.length - linkKinds} kinds of spot piece, and the limit is {maxSpotKinds}"]) ++
  (if G.map.spotCount ≤ maxSpots then [] else [s!"{G.map.spotCount} spots, and the limit is {maxSpots}"]) ++
  (if G.map.links.length ≤ maxLinks then [] else [s!"{G.map.links.length} links, and the limit is {maxLinks}"]) ++
  (if G.map.regions.length ≤ maxTiles then [] else [s!"{G.map.regions.length} tiles, and the limit is {maxTiles}"]) ++
  (if G.foundingLaws.length ≤ maxLaws then [] else [s!"{G.foundingLaws.length} founding laws, and the limit is {maxLaws}"])

/-! ## Opponents -/

/-- A named way to play: a strategy of the pool and its weights. -/
structure Opponent where
  name : String
  strategy : Strategy
  weights : Weights
  deriving Inhabited

/-- `fair` accepts an offer only if it helps its next build and counts what it pays. `closed` refuses every offer.
Both are the hand bot's code, and the weights are those of the evolution runs. -/
def opponents : List Opponent :=
  (Evolved.pool.map fun st => { name := st.name, strategy := st, weights := .default }) ++
  [ { name := "fair", strategy := hand, weights := { acceptGoods := 1, acceptNeed := 1, acceptMargin := 1 } }
  , { name := "closed", strategy := hand, weights := { acceptMargin := 10 } } ]

/-- What plays a seat. `none` is the caller. `setup` plays until the setup turns are over, and `play` after. -/
structure SeatPlan where
  setup : Option Opponent
  play : Option Opponent
  deriving Inhabited

/-! ## Settings -/

/-- Who decides a caller's votes. -/
inductive VoteMode where
  /-- A coin, inside the environment. The policy never sees a vote. -/
  | random
  /-- The hand bot's yes-or-no check, `lawOk`, inside the environment. The policy never sees a vote. -/
  | bot
  /-- The caller's policy. Votes are decisions like any other. -/
  | policy
  deriving BEq, Inhabited

/-- The order of the rows of `resources` and `kinds`. -/
inductive SlotOrder where
  /-- A new order each game, so that no row always means the same thing. -/
  | shuffled
  /-- The order the game lists them in. -/
  | game
  deriving BEq, Inhabited

/-- The named switches. `rl/OBSERVATIONS.md` says what each does. -/
structure Settings where
  /-- A law is put to a vote at the start of a turn with a chance of 1 in this. 0 never does. -/
  lawEvery : Nat := 8
  voteMode : VoteMode := .policy
  /-- Add the table of moves to the observation. -/
  moveRows : Bool := false
  /-- Fill the preview columns of the open proposal. -/
  preview : Bool := true
  /-- Deal a new map each game: the same board, with resources and numbers shuffled between tiles. -/
  randomMap : Bool := true
  slotOrder : SlotOrder := .shuffled
  /-- The reward for winning. -/
  rewardWin : Float := 1.0
  /-- The reward for final standing: this much for first, minus this much for last, even steps between. -/
  rewardStanding : Float := 0.25
  /-- A small reward for each point gained, as a share of the target. Off by default. -/
  shapingPoints : Float := 0.0
  deriving Inhabited

/-! ## One game's rows -/

/-- What stays fixed for one game once the map and the row order are chosen. -/
structure Episode where
  /-- The resource of each row of `resources`. -/
  rowRes : Array String
  /-- The piece of each row of `kinds`. Empty means no such piece yet. A law can add one. -/
  rowKind : Array String
  /-- The tiles that pay each spot, as a row of `resources` and pips. -/
  spotRes : Array (List (Nat × Nat))
  /-- The row of `resources` of each tile. -/
  tileRes : Array Nat
  deriving Inhabited

def Episode.resRow? (ep : Episode) (r : Res) : Option Nat := ep.rowRes.findIdx? (· == r)
def Episode.kindRow? (ep : Episode) (k : PieceKind) : Option Nat := ep.rowKind.findIdx? (· == k)

/-- Rows for pieces that do not have one yet: a link piece in the link rows, and any other in the spot rows. -/
def Episode.seat (ep : Episode) (pieces : List PieceDef) : Episode :=
  { ep with rowKind := pieces.foldl (fun rows d =>
      if rows.contains d.name then rows else
      let isLink := match d.placement with | .link => true | _ => false
      let start := if isLink then 0 else maxLinkKinds
      let stop := if isLink then maxLinkKinds else maxKinds
      match (List.range (stop - start)).find? (fun i => rows.getD (start + i) "x" == "") with
      | some i => rows.setIfInBounds (start + i) d.name
      | none => rows) ep.rowKind }

/-- A number fixed by a seed and an index. It uses nothing of the game's dice. -/
def mix (seed index : Nat) : UInt64 :=
  scramble (scramble (UInt64.ofNat seed ^^^ 0x5851F42D4C957F2D) + UInt64.ofNat index)

/-- This list in an order fixed by the seed. -/
def shuffled {α : Type} (xs : Array α) (seed : Nat) : Array α := Id.run do
  let mut a := xs
  let mut i := a.size
  while i > 1 do
    let j := (mix seed i).toNat % i
    a := a.swapIfInBounds (i - 1) j
    i := i - 1
  return a

/-- The rows of a game: the resources in some order, and its pieces in some order within the link and spot rows. -/
def Episode.make (G : GameDef) (order : SlotOrder) (seed : Nat) : Episode :=
  let names := (G.resources.map (·.name)).toArray
  let isLink (d : PieceDef) : Bool := match d.placement with | .link => true | _ => false
  let linkKinds := (G.pieces.filter isLink).toArray
  let spotKinds := (G.pieces.filter (!isLink ·)).toArray
  let (rowRes, linkKinds, spotKinds) := match order with
    | .game => (names, linkKinds, spotKinds)
    | .shuffled => (shuffled names (seed + 1), shuffled linkKinds (seed + 2), shuffled spotKinds (seed + 3))
  let empty : Array String := Array.replicate maxKinds ""
  let ep : Episode := { rowRes, rowKind := empty, spotRes := #[], tileRes := #[] }
  let rowRes' := fun (r : Res) => (rowRes.findIdx? (· == r)).getD 0
  let pay := paidRegions G
  let spotRes := (List.range G.map.spotCount).toArray.map fun v =>
    (pay.filter fun (t : Region) => t.spots.contains v).map fun (t : Region) => (rowRes' t.res, pips G t.number)
  ({ ep with spotRes, tileRes := (G.map.regions.map fun (t : Region) => rowRes' t.res).toArray }).seat
    (linkKinds.toList ++ spotKinds.toList)

/-! ## Maps -/

/-- The same board with resources and numbers shuffled between the tiles that pay. The shape of the map does not
change, and neither do the tiles that pay nothing. -/
def randomMap (G : GameDef) (seed : Nat) : GameDef :=
  let paid (t : Region) : Bool := !markRes G t.res
  let tiles := G.map.regions.toArray
  let res := shuffled ((tiles.filter paid).map (·.res)) (seed + 11)
  let nums := shuffled ((tiles.filter paid).map (·.number)) (seed + 12)
  let (_, regions) := tiles.foldl (fun (acc : Nat × Array Region) t =>
      if paid t then
        (acc.1 + 1, acc.2.push { t with res := res.getD acc.1 t.res, number := nums.getD acc.1 t.number })
      else (acc.1, acc.2.push t)) (0, #[])
  { G with map := { G.map with regions := regions.toList } }

/-- The map's part of a board, for a game that differs from `G` only in which tile pays what. -/
def Board.remap (G' : GameDef) (T : Tables) : Board G' :=
  let touching (v : Nat) := (paidRegions G').filter (·.spots.contains v)
  let high := T.board.neighbours.size
  { spots := T.board.spots
    neighbours := T.board.neighbours
    balls := T.board.balls
    spotPips := (List.range high).toArray.map fun v => ((touching v).map fun r => pips G' r.number).sum
    spotGoods := (List.range high).toArray.map fun v => ((touching v).map (·.res)).eraseDups.length }

end CharterRL
