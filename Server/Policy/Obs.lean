import Server.BotCore
import Server.Policy.Layout

/-!
# Observations and actions for the trained policy

The observation builder and the action decoding of the training harness (`rl/lean/CharterRL/` on branch
`rl-harness`, layout version 1), brought across with only what one decision needs:

- `Tables`, `Episode`: what is fixed for a game. Rows of `resources` and `kinds` are in the game's own order
  (`SlotOrder.game` in training; training shuffled them, so every order is one it has seen).
- `legal`, `decode`: the actions on offer, each asked of the engine, and the event for an action.
- `template`, `observe`: the numbers the network reads, for one seat.

Removed: the table of moves (off in training), the environment's law library, rewards, opponents, random maps.
The code that is kept is the harness's, line for line, so `rl/lean/CharterRL/Obs.lean` at `e466f9f` is the
reference. Nothing here reads `State.seed`.
-/

namespace CharterServer.Policy
open Charter CharterServer CharterServer.Bots

variable {G : GameDef}

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

private instance : Inhabited Region := ⟨{ res := "", number := 0, spots := [] }⟩

/-! ## What the observation needs about a game before it starts -/

/-- What never changes for a game. -/
structure Tables where
  G : GameDef
  board : Board G
  /-- Each spot's place on the board, from -1 to 1. -/
  spotXY : Array (Float × Float)
  /-- Each link's ends. -/
  links : Array (Nat × Nat)
  /-- The links that start at a spot, as the other end and the link's place. -/
  linkFrom : Array (List (Nat × Nat))
  /-- Some law in force can read a declared number, so declaring is offered. -/
  declares : Bool

/-- Spots' places on the board, from -1 to 1. -/
def normalised (points : List (Float × Float)) : Array (Float × Float) :=
  let top := points.foldl (fun m p => max m (max p.1.abs p.2.abs)) 0
  let top := if top == 0 then 1 else top
  points.toArray.map fun p => (p.1 / top, p.2 / top)

/-- The tables of a game. `spotXY` is each spot's place on the screen, any scale. `declares` says whether some law
in force reads a declared number. -/
def Tables.make (G : GameDef) (spotXY : List (Float × Float)) (declares : Bool) : Tables :=
  let links := G.map.links.toArray
  let high := G.map.spotCount
  let linkFrom := links.foldl (fun (acc : Nat × Array (List (Nat × Nat))) l =>
      (acc.1 + 1, acc.2.modify l.1 (· ++ [(l.2, acc.1)]))) (0, Array.replicate high []) |>.2
  { G, board := Board.of G, spotXY := normalised spotXY, links, linkFrom, declares }

/-- Why this game does not fit the layout the network was trained on, if it does not. Empty means it fits.
`pieces` are the kinds of piece in force now: laws can add kinds. -/
def problemsOf (G : GameDef) (pieces : List PieceDef) (lawCount : Nat) : List String :=
  let linkKinds := (pieces.filter fun d => match d.placement with | .link => true | _ => false).length
  (if G.resources.length ≤ maxRes then [] else [s!"{G.resources.length} resources, and the limit is {maxRes}"]) ++
  (if linkKinds ≤ maxLinkKinds then [] else [s!"{linkKinds} kinds of link piece, and the limit is {maxLinkKinds}"]) ++
  (if pieces.length - linkKinds ≤ maxSpotKinds then [] else [s!"{pieces.length - linkKinds} kinds of spot piece, and the limit is {maxSpotKinds}"]) ++
  (if G.map.spotCount ≤ maxSpots then [] else [s!"{G.map.spotCount} spots, and the limit is {maxSpots}"]) ++
  (if G.map.links.length ≤ maxLinks then [] else [s!"{G.map.links.length} links, and the limit is {maxLinks}"]) ++
  (if G.map.regions.length ≤ maxTiles then [] else [s!"{G.map.regions.length} tiles, and the limit is {maxTiles}"]) ++
  (if lawCount ≤ maxLaws then [] else [s!"{lawCount} laws in force, and the limit is {maxLaws}"])

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

/-- The rows of a game: the resources and pieces in the game's own order, link pieces first. -/
def Episode.make (G : GameDef) : Episode :=
  let names := (G.resources.map (·.name)).toArray
  let isLink (d : PieceDef) : Bool := match d.placement with | .link => true | _ => false
  let linkKinds := (G.pieces.filter isLink).toArray
  let spotKinds := (G.pieces.filter (!isLink ·)).toArray
  let rowRes := names
  let empty : Array String := Array.replicate maxKinds ""
  let ep : Episode := { rowRes, rowKind := empty, spotRes := #[], tileRes := #[] }
  let rowRes' := fun (r : Res) => (rowRes.findIdx? (· == r)).getD 0
  let pay := paidRegions G
  let spotRes := (List.range G.map.spotCount).toArray.map fun v =>
    (pay.filter fun (t : Region) => t.spots.contains v).map fun (t : Region) => (rowRes' t.res, pips G t.number)
  ({ ep with spotRes, tileRes := (G.map.regions.map fun (t : Region) => rowRes' t.res).toArray }).seat
    (linkKinds.toList ++ spotKinds.toList)

/-- What the environment waits for. -/
inductive Decision where
  /-- The game is over, or nothing can happen. -/
  | none
  /-- This seat votes on this law. -/
  | vote (seat id : Nat) (L : Law)
  /-- It is this seat's turn. -/
  | turn (seat : Nat)
  deriving Inhabited

/-- The seat that must decide. -/
def Decision.seat? : Decision → Option Nat
  | .none => Option.none
  | .vote seat _ _ => some seat
  | .turn seat => some seat

/-- The action for this move, if it has one. Offers, accepts and cancels do not. -/
def encodeMove (T : Tables) (ep : Episode) : Move → Option Nat
  | .endTurn => some actEnd
  | .bankTrade g h => do
    let i ← ep.resRow? g
    let j ← ep.resRow? h
    pure (actBank + i * maxRes + j)
  | .declare r n => do
    let i ← ep.resRow? r
    let l ← declareLevels.findIdx? (· == n)
    pure (actDeclare + i * declareLevels.size + l)
  | .place k (.spot v) => do
    let row ← ep.kindRow? k
    if row < maxLinkKinds || maxSpots ≤ v then Option.none
    else pure (actSpot + (row - maxLinkKinds) * maxSpots + v)
  | .place k (.link l) => do
    let row ← ep.kindRow? k
    let (_, at_) ← (T.linkFrom.getD l.1 []).find? (·.1 == l.2)
    if maxLinkKinds ≤ row then Option.none else pure (actLink + row * maxLinks + at_)
  | _ => Option.none

/-- The action for this event, for this decision. -/
def encode (T : Tables) (ep : Episode) (d : Decision) : Event → Option Nat
  | .move _ m => match d with
    | .turn _ => encodeMove T ep m
    | _ => Option.none
  | .vote _ id yes => match d with
    | .vote _ want _ => if id == want then some (if yes then actVoteYes else actVoteNo) else Option.none
    | _ => Option.none
  | _ => Option.none

/-- The event for this action, for this decision. `none` means this action is not on offer now, whatever the engine
would say: a vote when no vote is due, a move while a vote is due, a declaration in a game where no law reads one,
or a row with nothing in it. -/
def decode (T : Tables) (ep : Episode) (d : Decision) (a : Nat) : Option Event :=
  match d with
  | .none => Option.none
  | .vote seat id _ =>
    if a == actVoteNo then some (.vote seat id false)
    else if a == actVoteYes then some (.vote seat id true)
    else Option.none
  | .turn seat =>
    let some' (m : Move) : Option Event := some (.move seat m)
    if a == actEnd then some' .endTurn
    else if a < actBank then Option.none
    else if a < actDeclare then
      let i := a - actBank
      match ep.rowRes[i / maxRes]?, ep.rowRes[i % maxRes]? with
      | some g, some h => some' (.bankTrade g h)
      | _, _ => Option.none
    else if a < actLink then
      if !T.declares then Option.none else
      let i := a - actDeclare
      match ep.rowRes[i / declareLevels.size]?, declareLevels[i % declareLevels.size]? with
      | some r, some n => some' (.declare r n)
      | _, _ => Option.none
    else if a < actSpot then
      let i := a - actLink
      match ep.rowKind[i / maxLinks]?, T.links[i % maxLinks]? with
      | some k, some l => if k == "" then Option.none else some' (.place k (.link l))
      | _, _ => Option.none
    else if a < actSize then
      let i := a - actSpot
      let v := i % maxSpots
      match ep.rowKind[maxLinkKinds + i / maxSpots]? with
      | some k => if k == "" || T.G.map.spotCount ≤ v then Option.none else some' (.place k (.spot v))
      | none => Option.none
    else Option.none

/-- Keep the moves the engine takes, with their actions. -/
private def keep (T : Tables) (ep : Episode) (s : State G) (seat : Nat) (ms : List Move) : List (Nat × Event) :=
  ms.filterMap fun m =>
    if isLegal s seat m then (encodeMove T ep m).map (·, .move seat m) else Option.none

/-- Every action on offer now, with its event, by asking the engine. Ending the turn needs no asking: the rules
accept it on a seat's own turn, and theorem `endTurnNow_some` says that it cannot fail. -/
def legal (T : Tables) (ep : Episode) (ctx : Ctx G) (s : State G) (d : Decision) : List (Nat × Event) :=
  match d with
  | .none => []
  | .vote seat id _ =>
    [(actVoteNo, Event.vote seat id false), (actVoteYes, Event.vote seat id true)].filter fun x =>
      (Engine.step G s x.2).toOption.isSome
  | .turn seat =>
    let end_ : List (Nat × Event) := if s.isTurnOf seat then [(actEnd, .move seat .endTurn)] else []
    if s.phase == .setup then
      end_ ++ keep T ep s seat (setupPlaces ctx s seat)
    else
      let places := placesOf ctx s seat fun _ => true
      let names := ep.rowRes.toList
      let trades := names.flatMap fun g => names.filterMap fun h =>
        if g == h then Option.none else some (Move.bankTrade g h)
      let declares := if T.declares then
          names.flatMap fun r => declareLevels.toList.map (Move.declare r)
        else []
      end_ ++ keep T ep s seat (places ++ trades ++ declares)

/-- The mask of these actions. -/
def maskOf (acts : List (Nat × Event)) : ByteArray :=
  acts.foldl (fun m x => m.set! x.1 1) (ByteArray.mk (Array.replicate actSize 0))

/-- A count of goods on a scale that also fits a stock of 800: 1 is about 50. -/
def amtTable : FloatArray :=
  (List.range 2048).foldl (fun a n => a.push (Float.log (Float.ofNat (n + 1)) / 4)) FloatArray.empty

def amt (n : Nat) : Float := amtTable.get! (min n 2047)

private def ofNat (n : Nat) : Float := Float.ofNat n

/-- Write one number. -/
@[inline] private def put (a : FloatArray) (t : Table) (off row col : Nat) (x : Float) : FloatArray :=
  a.set! (off + row * t.width + col) x

/-! ## Where the columns are -/

private def oGlobal := offsetOf "global"
private def oSeats := offsetOf "seats"
private def oRes := offsetOf "resources"
private def oKinds := offsetOf "kinds"
private def oTiles := offsetOf "tiles"
private def oSpots := offsetOf "spots"
private def oLinks := offsetOf "links"
private def oLaws := offsetOf "laws"
private def oProposal := offsetOf "proposal"

private def cG (name : String) := tGlobal.col name
private def gVote := cG "decide_vote"
private def gSetup := cG "decide_setup"
private def gTurn := cG "decide_turn"
private def gRound := cG "round"
private def gRoundsLeft := cG "rounds_left"
private def gTarget := cG "target"
private def gSeats := cG "seats"
private def gBank := cG "bank_rate"
private def gDice := cG "dice_top"
private def gLast := cG "last_roll"
private def gActions := cG "actions_used"
private def gStep := cG "setup_step"
private def gTurnPos := cG "turn_pos"
private def gMyPos := cG "my_pos"
private def gLaws := cG "laws"
private def gOver := cG "moves_overflow"

private def cS (name : String) := tSeats.col name
private def sCurrent := cS "current"
private def sOrder := cS "order_pos"
private def sPoints := cS "points"
private def sToTarget := cS "to_target"
private def sGoods := cS "goods"
private def sIncome := cS "income"
private def sSpot := cS "spot_pieces"
private def sLink := cS "link_pieces"
private def sActions := cS "actions_used"

private def cR (name : String) := tResources.col name
private def rIsGood := cR "is_good"
private def rStock := cR "stock"
private def rBank := cR "bank"
private def rTreasury := cR "treasury"
private def rPips := cR "map_pips"
private def rTiles := cR "tiles"
private def rDemand := cR "demand"
private def rWorth := cR "worth"
private def rHolding := cR "holding"
private def rIncome := cR "income"
private def rDeclared := cR "declared"

private def cK (name : String) := tKinds.col name
private def kLink := cK "on_link"
private def kSpot := cK "on_spot"
private def kUpgrade := cK "on_upgrade"
private def kAttach := cK "on_attach"
private def kPoints := cK "points"
private def kYield := cK "yield"
private def kLimit := cK "limit"
private def kCostTotal := cK "cost_total"
private def kUnderPoints := cK "under_points"
private def kUnderYield := cK "under_yield"
private def kShort := cK "my_short"
private def kAfford := cK "my_afford"
private def kRoom := cK "my_room"
private def kCost := cK "cost"
private def kCount := cK "count"

private def cT (name : String) := tTiles.col name
private def tX := cT "x"
private def tY := cT "y"
private def tNumber := cT "number"
private def tPips := cT "pips"
private def tStock := cT "stock"
private def tDemand := cT "demand"
private def tWorth := cT "worth"
private def tMyIncome := cT "my_income"
private def tMyHolding := cT "my_holding"
private def tRes := cT "res"

private def cP (name : String) := tSpots.col name
private def pX := cP "x"
private def pY := cP "y"
private def pDegree := cP "degree"
private def pPips := cP "pips"
private def pGoods := cP "goods"
private def pDemand := cP "demand_value"
private def pNew := cP "new_for_me"
private def pFree := cP "free"
private def pReach := cP "reach_me"
private def pOccupied := cP "occupied"
private def pPiecePoints := cP "piece_points"
private def pPieceYield := cP "piece_yield"
private def pAttached := cP "attached"
private def pOwner := cP "owner"
private def pByRes := cP "pips_by_res"

private def cL (name : String) := tLinks.col name
private def lX := cL "x"
private def lY := cL "y"
private def lA := cL "end_a"
private def lB := cL "end_b"
private def lTaken := cL "taken"
private def lReach := cL "reach_me"
private def lFreeEnds := cL "free_ends"
private def lBest := cL "best_end_pips"
private def lOwner := cL "owner"

private def lawFounding := tLaws.col "founding"
private def lawShapeAt := tLaws.col "on_harvest"

private def cQ (name : String) := tProposal.col name
private def qShape := cQ "on_harvest"
private def qYes := cQ "yes_count"
private def qNeeded := cQ "yes_needed"
private def qDeciding := cQ "deciding"
private def qPreviewed := cQ "previewed"
private def qEnds := cQ "ends_game"
private def qBank := cQ "bank_rate_change"
private def qBy := cQ "by"
private def qVotedYes := cQ "voted_yes"
private def qVotedNo := cQ "voted_no"
private def qNet := cQ "next_turn_net"
private def qNow := cQ "now_net"
private def qPoints := cQ "points_change"
private def qMyNet := cQ "next_turn_my_net"
private def qCost := cQ "cost_change"

/-- `real` is column 0 of every table. -/
private def real := 0

/-! ## What stays fixed for a game -/

/-- Write the rows of the laws in force. It runs when the laws change. -/
def writeLaws (a : FloatArray) (G : GameDef) (laws : List (Nat × Law)) : FloatArray := Id.run do
  let mut a := a
  let founding := G.foundingLaws.length
  for row in [0:maxLaws] do
    match laws[row]? with
    | none =>
      for c in [0:tLaws.width] do a := put a tLaws oLaws row c 0
    | some (id, L) =>
      a := put a tLaws oLaws row real 1
      a := put a tLaws oLaws row lawFounding (if id < founding then 1 else 0)
      let mut c := lawShapeAt
      for x in Law.shape L do
        a := put a tLaws oLaws row c x
        c := c + 1
  return a

/-- Everything an observation of this game has before anyone moves. -/
def template (T : Tables) (ep : Episode) (G : GameDef) (seats : Nat) (_moveRows : Bool := false) : FloatArray := Id.run do
  let size := baseSize
  let mut a : FloatArray := (List.range size).foldl (fun a _ => a.push 0) FloatArray.empty
  a := put a tGlobal oGlobal 0 real 1
  a := put a tGlobal oGlobal 0 gTarget (ofNat G.targetPoints / 50)
  a := put a tGlobal oGlobal 0 gSeats (ofNat seats / ofNat maxSeats)
  a := put a tGlobal oGlobal 0 gDice (ofNat (G.diceCount * G.diceSides) / 24)
  for i in [0:seats] do
    a := put a tSeats oSeats i real 1
  -- Resources.
  let nres := ep.rowRes.size
  let tiles := G.map.regions.toArray
  for row in [0:nres] do
    let r := ep.rowRes[row]!
    let mine := tiles.filter (·.res == r)
    a := put a tResources oRes row real 1
    a := put a tResources oRes row rIsGood (if markRes G r then 0 else 1)
    a := put a tResources oRes row rStock (amt (G.stockOf r))
    a := put a tResources oRes row rPips (ofNat (mine.foldl (fun n t => n + pips G t.number) 0) / 36)
    a := put a tResources oRes row rTiles (ofNat mine.size / 12)
  -- Spots.
  let spotCount := G.map.spotCount
  let spotXY := T.spotXY
  let bestEnd (v : Nat) : Nat := ((ep.spotRes.getD v []).map (·.2)).sum
  for v in [0:spotCount] do
    let (x, y) := spotXY.getD v (0, 0)
    let pay := ep.spotRes.getD v []
    a := put a tSpots oSpots v real 1
    a := put a tSpots oSpots v pX x
    a := put a tSpots oSpots v pY y
    a := put a tSpots oSpots v pDegree (ofNat (T.board.neighbours.getD v []).length / 3)
    a := put a tSpots oSpots v pPips (ofNat (bestEnd v) / 15)
    a := put a tSpots oSpots v pGoods (ofNat (pay.map (·.1)).eraseDups.length / 3)
    for (r, n) in pay do
      let c := pByRes + r
      a := put a tSpots oSpots v c (a.get! (oSpots + v * tSpots.width + c) + ofNat n / 6)
  -- Tiles. A tile's place is the middle of its spots.
  for row in [0:tiles.size] do
    let t := tiles[row]!
    let count := Float.ofNat (max 1 t.spots.length)
    let (x, y) := t.spots.foldl (fun (p : Float × Float) v =>
      let (x, y) := spotXY.getD v (0, 0)
      (p.1 + x, p.2 + y)) (0, 0)
    a := put a tTiles oTiles row real 1
    a := put a tTiles oTiles row tX (x / count)
    a := put a tTiles oTiles row tY (y / count)
    a := put a tTiles oTiles row tNumber (ofNat t.number / 24)
    a := put a tTiles oTiles row tPips (ofNat (pips G t.number) / 6)
    a := put a tTiles oTiles row tStock (amt (G.stockOf t.res))
    a := put a tTiles oTiles row (tRes + ep.tileRes.getD row 0) 1
  -- Links.
  for i in [0:T.links.size] do
    let (p, q) := T.links[i]!
    let (x1, y1) := spotXY.getD p (0, 0)
    let (x2, y2) := spotXY.getD q (0, 0)
    a := put a tLinks oLinks i real 1
    a := put a tLinks oLinks i lX ((x1 + x2) / 2)
    a := put a tLinks oLinks i lY ((y1 + y2) / 2)
    a := put a tLinks oLinks i lA (ofNat p / ofNat maxSpots)
    a := put a tLinks oLinks i lB (ofNat q / ofNat maxSpots)
    a := put a tLinks oLinks i lBest (ofNat (max (bestEnd p) (bestEnd q)) / 15)
  return writeLaws a G G.startingLaws

/-! ## One decision -/

/-- A seat's place in the columns of this seat's view: this seat, then the others in turn order. -/
@[inline] private def ego (me seats q : Nat) : Nat := (q + seats - me) % seats

/-- What the books say each seat holds, by seat and row of `resources`. -/
private def holdings (ep : Episode) (s : State G) (seats : Nat) : Array Nat :=
  (List.range seats).foldl (fun acc q =>
    ep.rowRes.foldl (fun acc r => acc.push (s.balance (.player q) r)) acc) (Array.mkEmpty (seats * ep.rowRes.size))

/-- What the dice pay each seat's pieces, in pips times yield, by seat and row of `resources`. -/
private def incomes (ep : Episode) (rules : Rules) (s : State G) (seats : Nat) : Array Nat :=
  let nres := ep.rowRes.size
  s.pieces.foldl (fun acc x =>
    match x.loc with
    | .link _ => acc
    | .spot v =>
      let y := ((rules.piece? x.kind).map (·.yield)).getD 0
      if y == 0 then acc else
      (ep.spotRes.getD v []).foldl (fun acc (r, n) => acc.modify (x.owner * nres + r) (· + n * y)) acc)
    (Array.replicate (seats * nres) 0)

/-- Add what these entries pay each seat, in this view, and what they pay this seat of each resource. -/
private def addEntries (ep : Episode) (me seats : Nat) (es : List Entry) (sign : Float)
    (net myRes : Array Float) : Array Float × Array Float :=
  es.foldl (fun (acc : Array Float × Array Float) e =>
    let amount := sign * ofNat e.amount
    let row := (ep.resRow? e.res).getD 0
    let (net, myRes) := acc
    let (net, myRes) := match e.dst with
      | .player q =>
        (net.modify (ego me seats q) (· + amount), if q == me then myRes.modify row (· + amount) else myRes)
      | _ => (net, myRes)
    match e.src with
    | .player q =>
      (net.modify (ego me seats q) (· - amount), if q == me then myRes.modify row (· - amount) else myRes)
    | _ => (net, myRes)) (net, myRes)

/-- What the next turn change pays each seat and this seat's resources, averaged over the dice. -/
private def expectedTurn (ep : Episode) (s : State G) (me seats : Nat) (sign : Float)
    (net myRes : Array Float) : Array Float × Array Float :=
  let rolls := Scene.rollsOf G
  let ways := rolls.foldl (fun n r => n + pips G r) 0
  rolls.foldl (fun (acc : Array Float × Array Float) r =>
    addEntries ep me seats (Engine.predictNextTurn G s r) (sign * ofNat (pips G r) / ofNat (max 1 ways)) acc.1 acc.2)
    (net, myRes)

/-- The columns of the open proposal. -/
private def writeProposal (a : FloatArray) (ep : Episode) (preview : Bool) (s : State G) (me seats id : Nat) (L : Law) :
    FloatArray := Id.run do
  let mut a := a
  let w := tProposal
  let at_ (a : FloatArray) (c : Nat) (x : Float) := put a w oProposal 0 c x
  a := at_ a real 1
  let mut c := qShape
  for x in Law.shape L do
    a := at_ a c x
    c := c + 1
  let some p := s.openProposal? id | return a
  a := at_ a (qBy + ego me seats p.by_) 1
  for (q, yes) in p.votes do
    a := at_ a ((if yes then qVotedYes else qVotedNo) + ego me seats q) 1
  a := at_ a qYes (ofNat p.yesCount / ofNat maxSeats)
  let needed := seats / 2 + 1
  a := at_ a qNeeded (ofNat (needed - min needed p.yesCount) / ofNat maxSeats)
  a := at_ a qDeciding (if Engine.isDecidingVote s p me true then 1 else 0)
  a := at_ a qEnds (if L.clauses.any Clause.isEndGame then 1 else 0)
  if !preview then return a
  a := at_ a qPreviewed 1
  let s' := s.withLaw id L
  let zero (n : Nat) : Array Float := Array.replicate n 0
  let (net, myRes) := expectedTurn ep s me seats (-1) (zero maxSeats) (zero maxRes)
  let (net, myRes) := expectedTurn ep s' me seats 1 net myRes
  let (nowNet, _) := addEntries ep me seats (s.decreeEntries L) 1 (zero maxSeats) (zero maxRes)
  for i in [0:seats] do
    let q := (me + i) % seats
    a := at_ a (qNet + i) (net[i]! / 4)
    a := at_ a (qNow + i) (nowNet[i]! / 4)
    a := at_ a (qPoints + i) ((ofNat (s'.pointsOf q) - ofNat (s.pointsOf q)) / 5)
  for r in [0:ep.rowRes.size] do
    a := at_ a (qMyNet + r) (myRes[r]! / 4)
  a := at_ a qBank ((ofNat s'.rules.bankRate - ofNat s.rules.bankRate) / 8)
  for row in [0:maxKinds] do
    let k := ep.rowKind[row]!
    if k != "" then
      let total (x : State G) : Nat := (x.costOf k).foldl (fun n y => n + y.2) 0
      a := at_ a (qCost + row) ((ofNat (total s') - ofNat (total s)) / 8)
  return a

/-- The whole observation for the seat that must decide. `base` is the game's template. -/
def observe (T : Tables) (ep : Episode) (ctx : Ctx G) (base : FloatArray) (s : State G)
    (d : Decision) : FloatArray := Id.run do
  let some me := d.seat? | return base
  let mut a := base
  let seats := s.turnOrder.length
  let rules := s.rules
  let nres := ep.rowRes.size
  let held := holdings ep s seats
  let income := incomes ep rules s seats
  -- Global.
  let g (a : FloatArray) (c : Nat) (x : Float) := put a tGlobal oGlobal 0 c x
  a := g a (match d with
    | .vote .. => gVote
    | _ => if s.phase == .setup then gSetup else gTurn) 1
  a := g a gRound (ofNat s.round / 60)
  a := g a gRoundsLeft (ofNat (G.rounds - min G.rounds s.round) / 60)
  a := g a gBank (ofNat rules.bankRate / 8)
  a := g a gLast (ofNat (s.lastRoll.getD 0) / 24)
  a := g a gActions (ofNat (s.actionsThisTurn me) / 20)
  a := g a gStep (if s.phase == .setup then ofNat (s.actionsThisTurn me) / 4 else 0)
  a := g a gTurnPos (ofNat s.turnIndex / ofNat maxSeats)
  a := g a gMyPos (ofNat me / ofNat maxSeats)
  a := g a gLaws (ofNat s.laws.length / ofNat maxLaws)
  -- Resources. Demand is how much of it all pieces cost together.
  let mut demand : Array Nat := Array.replicate nres 0
  for d in rules.pieces do
    for (r, n) in d.cost do
      if let some row := ep.resRow? r then demand := demand.modify row (· + n)
  let target := ofNat (max 1 G.targetPoints)
  let mut goodsBySeat : Array Nat := Array.replicate seats 0
  let mut incomeBySeat : Array Nat := Array.replicate seats 0
  for row in [0:nres] do
    let r := ep.rowRes[row]!
    a := put a tResources oRes row rBank (amt (s.balance .bank r))
    a := put a tResources oRes row rTreasury (amt (s.balance .treasury r))
    a := put a tResources oRes row rDemand (ofNat demand[row]! / 8)
    let worth := ((rules.worth.find? (·.1 == r)).map (·.2)).getD 0
    a := put a tResources oRes row rWorth (ofNat worth / 4)
    for q in [0:seats] do
      let i := ego me seats q
      let h := held[q * nres + row]!
      let inc := income[q * nres + row]!
      a := put a tResources oRes row (rHolding + i) (amt h)
      a := put a tResources oRes row (rIncome + i) (ofNat inc / 36)
      a := put a tResources oRes row (rDeclared + i) (amt (s.declared q r))
      goodsBySeat := goodsBySeat.modify q (· + h)
      incomeBySeat := incomeBySeat.modify q (· + inc)
  -- Tiles.
  let tileCount := G.map.regions.length
  for row in [0:tileCount] do
    let r := ep.tileRes[row]!
    a := put a tTiles oTiles row tDemand (ofNat demand[r]! / 8)
    let worth := ((rules.worth.find? (·.1 == (ep.rowRes[r]!))).map (·.2)).getD 0
    a := put a tTiles oTiles row tWorth (ofNat worth / 4)
    a := put a tTiles oTiles row tMyIncome (ofNat income[me * nres + r]! / 36)
    a := put a tTiles oTiles row tMyHolding (amt held[me * nres + r]!)
  -- Spots and links, from the map first, then from each piece.
  let free := freeMap ctx s
  let reach := reachMap ctx s me
  let spotCount := G.map.spotCount
  for v in [0:spotCount] do
    if free.getD v false then a := put a tSpots oSpots v pFree 1
    if reach.getD v false then a := put a tSpots oSpots v pReach 1
    let pay := ep.spotRes.getD v []
    let mut value := 0
    let mut fresh := 0
    for (r, n) in pay do
      value := value + n * demand[r]!
      if income[me * nres + r]! == 0 then fresh := fresh + n
    a := put a tSpots oSpots v pDemand (ofNat value / 60)
    a := put a tSpots oSpots v pNew (ofNat fresh / 15)
  let linkCount := T.links.size
  for i in [0:linkCount] do
    let (p, q) := T.links[i]!
    if reach.getD p false || reach.getD q false then a := put a tLinks oLinks i lReach 1
    let ends := (if free.getD p false then 1 else 0) + (if free.getD q false then 1 else 0)
    a := put a tLinks oLinks i lFreeEnds (ofNat ends / 2)
  let mut kindCount : Array Nat := Array.replicate (maxKinds * maxSeats) 0
  let mut spotPieces : Array Nat := Array.replicate seats 0
  let mut linkPieces : Array Nat := Array.replicate seats 0
  for x in s.pieces do
    let i := ego me seats x.owner
    if let some row := ep.kindRow? x.kind then
      kindCount := kindCount.modify (row * maxSeats + i) (· + 1)
    match x.loc with
    | .spot v =>
      spotPieces := spotPieces.modify x.owner (· + 1)
      let e := rules.piece? x.kind
      let off := oSpots + v * tSpots.width
      a := a.set! (off + pOccupied) 1
      a := a.set! (off + pOwner + i) 1
      a := a.set! (off + pPiecePoints) (a.get! (off + pPiecePoints) + ofNat ((e.map (·.points)).getD 0) / 5)
      a := a.set! (off + pPieceYield) (a.get! (off + pPieceYield) + ofNat ((e.map (·.yield)).getD 0) / 3)
      match e.map (·.placement) with
      | some (Placement.attach _) => a := a.set! (off + pAttached) (a.get! (off + pAttached) + 1 / 3)
      | _ => pure ()
    | .link l =>
      linkPieces := linkPieces.modify x.owner (· + 1)
      match (T.linkFrom.getD l.1 []).find? (·.1 == l.2) with
      | some (_, k) =>
        a := put a tLinks oLinks k lTaken 1
        a := put a tLinks oLinks k (lOwner + i) 1
      | none => pure ()
  -- Seats.
  for q in [0:seats] do
    let i := ego me seats q
    let points := s.pointsOf q
    a := put a tSeats oSeats i sCurrent (if s.currentSeat == some q then 1 else 0)
    a := put a tSeats oSeats i sOrder (ofNat q / ofNat maxSeats)
    a := put a tSeats oSeats i sPoints (ofNat points / target)
    a := put a tSeats oSeats i sToTarget (ofNat (G.targetPoints - min G.targetPoints points) / target)
    a := put a tSeats oSeats i sGoods (amt goodsBySeat[q]!)
    a := put a tSeats oSeats i sIncome (ofNat incomeBySeat[q]! / 36)
    a := put a tSeats oSeats i sSpot (ofNat spotPieces[q]! / 16)
    a := put a tSeats oSeats i sLink (ofNat linkPieces[q]! / 16)
    a := put a tSeats oSeats i sActions (ofNat (s.actionsThisTurn q) / 20)
  -- Kinds.
  for row in [0:maxKinds] do
    let k := ep.rowKind[row]!
    if k == "" then continue
    let some e := rules.piece? k | continue
    let w := tKinds
    a := put a w oKinds row real 1
    let under : Option PieceDef := match e.placement with
      | .link | .spot => Option.none
      | .upgrade j | .attach j => rules.piece? j
    a := put a w oKinds row (match e.placement with
      | .link => kLink | .spot => kSpot | .upgrade _ => kUpgrade | .attach _ => kAttach) 1
    a := put a w oKinds row kPoints (ofNat e.points / 5)
    a := put a w oKinds row kYield (ofNat e.yield / 3)
    a := put a w oKinds row kLimit (ofNat e.limit / 16)
    if let some u := under then
      a := put a w oKinds row kUnderPoints (ofNat u.points / 5)
      a := put a w oKinds row kUnderYield (ofNat u.yield / 3)
    let mut total := 0
    let mut short := 0
    for (r, n) in e.cost do
      total := total + n
      if let some col := ep.resRow? r then
        a := put a w oKinds row (kCost + col) (ofNat n / 4)
        short := short + (n - min n held[me * nres + col]!)
    a := put a w oKinds row kCostTotal (ofNat total / 8)
    a := put a w oKinds row kShort (ofNat short / 8)
    a := put a w oKinds row kAfford (if short == 0 then 1 else 0)
    for i in [0:seats] do
      a := put a w oKinds row (kCount + i) (ofNat kindCount[row * maxSeats + i]! / 16)
    a := put a w oKinds row kRoom (if kindCount[row * maxSeats]! < e.limit then 1 else 0)
  -- The open proposal, when this seat is voting on it.
  match d with
  | .vote _ id L => a := writeProposal a ep true s me seats id L
  | _ => pure ()
  return a

end CharterServer.Policy
