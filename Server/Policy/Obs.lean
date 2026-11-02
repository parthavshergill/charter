import Server.BotCore
import Server.Policy.Layout

/-!
# Observations and actions for the trained policy

The observation builder and the action decoding of the training harness (`rl/lean/CharterRL/` at commit `3b98ee8`
on branch `rl-harness`, layout version 2), brought across with only what one decision needs:

- `Tables`, `Episode`: what is fixed for a game. Rows of `resources` and `kinds` are in the game's own order
  (`SlotOrder.game` in training; training shuffled them, so every order is one it has seen).
- `placeList`, `legal`, `decode`: the actions on offer, each asked of the engine, and the event for an action.
- `template`, `observe`: the numbers the network reads, for one seat.

Kept: the optional table of moves (`move_rows`), in both orders the harness has used (`rankedMoves`: off for
checkpoints trained before `5fde545`), and the harness's mask rules: no early end turn in setup while a placement is
legal, no bank trade that undoes the last one, and, when the checkpoint trained with them, `prune_declares` and
`declare_once_per_turn`.
Removed: the environment's law library, rewards, opponents, random maps.
The code that is kept is the harness's, line for line. `scripts/policy_obs_compare.sh` checks that it writes the
same numbers as the harness on the same games: on 470 decisions over every world they match, except the law-shape
columns of AI Bubble's and Pirate Republic's founding laws, which `main` rewrote after `89a3a51` (`f78dddd`).
Nothing here reads `State.seed`.
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

mutual
  /-- The goods whose declarations this number reads. `.harvested` stands for "a good not named here". -/
  def declaredRefsE : Expr → List ResRef
    | .declared _ r => [r]
    | .add a b | .sub a b | .mul a b | .min a b | .max a b | .divBy a b => declaredRefsE a ++ declaredRefsE b
    | .div a _ => declaredRefsE a
    | .totalOver c a | .mostOver c a | .leastOver c a => declaredRefsC c ++ declaredRefsE a
    | _ => []

  def declaredRefsC : Cond → List ResRef
    | .lt a b | .le a b | .eq a b => declaredRefsE a ++ declaredRefsE b
    | .and a b | .or a b => declaredRefsC a ++ declaredRefsC b
    | .not c => declaredRefsC c
    | _ => []
end

mutual
  def declaredRefsF : Effect → List ResRef
    | .transfer _ _ _ amount => declaredRefsE amount
    | .movePiece .. => []
    | .forEach c body | .when c body => declaredRefsC c ++ declaredRefsAll body

  def declaredRefsAll : List Effect → List ResRef
    | [] => []
    | e :: es => declaredRefsF e ++ declaredRefsAll es
end

/-- The goods whose declarations this law reads, or `none` if it reads one it does not name (`harvested`), so it
could read any. -/
def Law.declaredGoods (L : Law) : Option (List Res) :=
  let refs := L.clauses.flatMap fun c => declaredRefsAll c.effects
  refs.foldl (fun acc r => match acc, r with
    | some xs, .lit x => some (if xs.contains x then xs else xs ++ [x])
    | _, _ => none) (some [])

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
  /-- Declaring is offered. The candidate was trained with `declare_always`, so it is always on. -/
  declares : Bool := true

/-- Spots' places on the board, from -1 to 1. -/
def normalised (points : List (Float × Float)) : Array (Float × Float) :=
  let top := points.foldl (fun m p => max m (max p.1.abs p.2.abs)) 0
  let top := if top == 0 then 1 else top
  points.toArray.map fun p => (p.1 / top, p.2 / top)

/-- The tables of a game. `spotXY` is each spot's place on the screen, any scale. -/
def Tables.make (G : GameDef) (spotXY : List (Float × Float)) : Tables :=
  let links := G.map.links.toArray
  let high := G.map.spotCount
  let linkFrom := links.foldl (fun (acc : Nat × Array (List (Nat × Nat))) l =>
      (acc.1 + 1, acc.2.modify l.1 (· ++ [(l.2, acc.1)]))) (0, Array.replicate high []) |>.2
  { G, board := Board.of G, spotXY := normalised spotXY, links, linkFrom }

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

/-- Rows for pieces that do not have one yet: the first empty row. A game has at most `maxKinds` kinds, counting
those laws add, so there is always one. -/
def Episode.seat (ep : Episode) (pieces : List PieceDef) : Episode :=
  { ep with rowKind := pieces.foldl (fun rows d =>
      if rows.contains d.name then rows else
      match (List.range maxKinds).find? (fun i => rows.getD i "x" == "") with
      | some i => rows.setIfInBounds i d.name
      | none => rows) ep.rowKind }

/-- The rows of a game: the resources and pieces in the game's own order (the harness's `SlotOrder.game`). -/
def Episode.make (G : GameDef) : Episode :=
  let names := (G.resources.map (·.name)).toArray
  let kinds := G.pieces.toArray
  let rowRes := names
  let empty : Array String := Array.replicate maxKinds ""
  let ep : Episode := { rowRes, rowKind := empty, spotRes := #[], tileRes := #[] }
  let rowRes' := fun (r : Res) => (rowRes.findIdx? (· == r)).getD 0
  let pay := paidRegions G
  let spotRes := (List.range G.map.spotCount).toArray.map fun v =>
    (pay.filter fun (t : Region) => t.spots.contains v).map fun (t : Region) => (rowRes' t.res, pips G t.number)
  ({ ep with spotRes, tileRes := (G.map.regions.map fun (t : Region) => rowRes' t.res).toArray }).seat kinds.toList

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

/-! ## Placements

A placement has no fixed action. The legal placements of a decision are put in `placeOrder` and the first
`maxPlaceRows` of them get rows of `places`, and actions `actPlace + i`. The order does not depend on names or on
the order a game lists things in, so it is the same under renaming:
1. by placement: replacing a piece, then attaching to one, then a new piece on a spot, then a piece on a link;
2. then by the pips of the spot (for a link, its better free end), most first;
3. then by the spot, or the link's ends, and then by the kind's row. -/

/-- What a placement is, for the order: its placement, its value, where, and its kind's row. -/
def placeKey (ctx : Ctx G) (ep : Episode) (rules : Rules) (free : Array Bool) : Move → Nat × Nat × Nat × Nat × Nat
  | .place k loc =>
    let row := (ep.kindRow? k).getD maxKinds
    let pipsAt (v : Nat) := ctx.board.spotPips.getD v 0
    let cls := match (rules.piece? k).map (·.placement) with
      | some (Placement.upgrade _) => 0
      | some (Placement.attach _) => 1
      | some Placement.spot => 2
      | _ => 3
    match loc with
    | .spot v => (cls, 1000 - pipsAt v, v, 0, row)
    | .link (a, b) =>
      let end_ (v : Nat) := if free.getD v false then pipsAt v else 0
      (cls, 1000 - max (end_ a) (end_ b), min a b, max a b, row)
  | _ => (9, 0, 0, 0, 0)

private def keyLt (a b : Nat × Nat × Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && (a.2.2.1 < b.2.2.1 ||
    (a.2.2.1 == b.2.2.1 && (a.2.2.2.1 < b.2.2.2.1 || (a.2.2.2.1 == b.2.2.2.1 && a.2.2.2.2 < b.2.2.2.2)))))))

/-- Every legal placement of this seat now, in `placeOrder`. Rows of `places` are the first `maxPlaceRows`. -/
def placeList (ctx : Ctx G) (ep : Episode) (s : State G) (seat : Nat) (free reach : Array Bool) : Array Move :=
  let cands := if s.phase == .setup then setupPlaces ctx s seat
    else placesWith ctx s seat (Thunk.pure free) (Thunk.pure reach) fun _ => true
  let ok := (cands.filter fun m => (match m with | .place .. => true | _ => false) && isLegal s seat m).toArray
  let keyed := ok.map fun m => (placeKey ctx ep s.rules free m, m)
  (keyed.qsort fun x y => keyLt x.1 y.1).map (·.2)

/-- The action for this move, if it has one. Offers, accepts and cancels do not, nor a placement without a row. -/
def encodeMove (ep : Episode) (places : Array Move) : Move → Option Nat
  | .endTurn => some actEnd
  | .bankTrade g h => do
    let i ← ep.resRow? g
    let j ← ep.resRow? h
    pure (actBank + i * maxRes + j)
  | .declare r n => do
    let i ← ep.resRow? r
    let l ← declareLevels.findIdx? (· == n)
    pure (actDeclare + i * declareLevels.size + l)
  | m@(.place ..) => do
    let i ← places.findIdx? (· == m)
    if i < maxPlaceRows then pure (actPlace + i) else Option.none
  | _ => Option.none

/-- The action for this event, for this decision. -/
def encode (ep : Episode) (places : Array Move) (d : Decision) : Event → Option Nat
  | .move _ m => match d with
    | .turn _ => encodeMove ep places m
    | _ => Option.none
  | .vote _ id yes => match d with
    | .vote _ want _ => if id == want then some (if yes then actVoteYes else actVoteNo) else Option.none
    | _ => Option.none
  | _ => Option.none

/-- The event for this action, for this decision. `places` is the decision's `placeList`. `none` means this action
is not on offer now, whatever the engine would say: a vote when no vote is due, a move while a vote is due, a
declaration in a game where no law reads one, or a row with nothing in it. -/
def decode (T : Tables) (ep : Episode) (places : Array Move) (d : Decision) (a : Nat) : Option Event :=
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
    else if a < actPlace then
      if !T.declares then Option.none else
      let i := a - actDeclare
      match ep.rowRes[i / declareLevels.size]?, declareLevels[i % declareLevels.size]? with
      | some r, some n => some' (.declare r n)
      | _, _ => Option.none
    else if a < actSize then (places[a - actPlace]?).map (.move seat ·)
    else Option.none

/-- The goods whose declarations some law in force or open law proposal reads, or `none` if one of them could read
any good. -/
def declaredRead (s : State G) : Option (List Res) :=
  let laws := s.laws.map (·.2) ++ s.openProposals.filterMap fun p => match p.body with
    | .law L => some L
    | .deal _ => Option.none
  laws.foldl (fun acc L => match acc, Policy.Law.declaredGoods L with
    | some xs, some ys => some (xs ++ ys.filter (!xs.contains ·))
    | _, _ => Option.none) (some [])

/-- A declaration changes something: it is not the number this seat has already declared of this good, and some law
reads that good's declarations. For `pruneDeclares`. -/
def declareChanges (s : State G) (seat : Nat) (r : Res) (n : Nat) : Bool :=
  s.declared seat r != n &&
    match declaredRead s with
    | some rs => rs.contains r
    | Option.none => true

/-- Every action on offer now, with its event, by asking the engine. Ending the turn needs no asking: the rules
accept it on a seat's own turn, and theorem `endTurnNow_some` says that it cannot fail. Placements come from
`places`, which `placeList` made by asking the engine about each. -/
def legal (T : Tables) (ep : Episode) (places : Array Move) (s : State G) (d : Decision)
    (undo : Option (Res × Res) := Option.none) (prune : Bool := false) (declaredNow : List Res := []) :
    List (Nat × Event) :=
  match d with
  | .none => []
  | .vote seat id _ =>
    [(actVoteNo, Event.vote seat id false), (actVoteYes, Event.vote seat id true)].filter fun x =>
      (Engine.step G s x.2).toOption.isSome
  | .turn seat =>
    let end_ : List (Nat × Event) := if s.isTurnOf seat then [(actEnd, .move seat .endTurn)] else []
    let rows := ((places.toList.take maxPlaceRows).zipIdx).map fun (m, i) => (actPlace + i, Event.move seat m)
    -- In setup, end turn is offered only when nothing can be placed: the engine allows ending a setup turn early,
    -- but that gives up a free opening piece, and policies kept doing it.
    if s.phase == .setup then (if rows.isEmpty then end_ else []) ++ rows else
    let names := ep.rowRes.toList
    -- `undo` is the trade that would reverse this seat's last bank trade of this turn: never worth making, since the
    -- bank takes its rate both ways, so it is not offered (the engine would accept it).
    let trades := names.flatMap fun g => names.filterMap fun h =>
      if g == h || undo == some (g, h) then Option.none else some (Move.bankTrade g h)
    let declares := if T.declares then names.flatMap fun r => declareLevels.toList.filterMap fun n =>
        if prune && (!declareChanges s seat r n || declaredNow.contains r) then Option.none
        else some (Move.declare r n) else []
    let others := (trades ++ declares).filterMap fun m =>
      if isLegal s seat m then (encodeMove ep places m).map (·, .move seat m) else Option.none
    end_ ++ others ++ rows

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
private def oSpots := offsetOf "spots"
private def oLaws := offsetOf "laws"
private def oProposal := offsetOf "proposal"
private def oPlaces := offsetOf "places"
private def oMoves := baseSize

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
private def gPlaces := cG "places"
private def gPlaceOver := cG "place_overflow"
private def gSpots := cG "spots"
private def gLinks := cG "links"

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

private def cP (name : String) := tSpots.col name
private def pX := cP "x"
private def pY := cP "y"
private def pDegree := cP "degree"
private def pPips := cP "pips"
private def pGoods := cP "goods"
private def pTiles := cP "tiles"
private def pLinksOpen := cP "links_open"
private def pLinksMine := cP "links_mine"
private def pLinksOf := cP "links_of"
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

private def cPl (name : String) := tPlaces.col name
private def plLink := cPl "on_link"
private def plSpot := cPl "on_spot"
private def plUpgrade := cPl "on_upgrade"
private def plAttach := cPl "on_attach"
private def plAt := cPl "at"
private def plAtB := cPl "at_b"
private def plX := cPl "x"
private def plY := cPl "y"
private def plPips := cPl "pips"
private def plGoods := cPl "goods"
private def plDemand := cPl "demand_value"
private def plNew := cPl "new_for_me"
private def plFreeEnds := cPl "free_ends"
private def plReach := cPl "reach_me"
private def plPoints := cPl "points_gain"
private def plYield := cPl "yield_gain"
private def plCostTotal := cPl "cost_total"
private def plShort := cPl "my_short"
private def plKind := cPl "kind"

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

private def cM (name : String) := tMoves.col name
private def mAction := cM "action"
private def mEnd := cM "is_end"
private def mVoteNo := cM "is_vote_no"
private def mVoteYes := cM "is_vote_yes"
private def mBank := cM "is_bank"
private def mDeclare := cM "is_declare"
private def mLink := cM "is_link"
private def mSpot := cM "is_spot"
private def mUpgrade := cM "is_upgrade"
private def mAttach := cM "is_attach"
private def mExpected := cM "expected"
private def mEnds := cM "ends_game"
private def mWin := cM "i_win"
private def mPoints := cM "points"
private def mGoods := cM "goods"
private def mMyHolding := cM "my_holding"
private def mMyIncome := cM "my_income"

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
def template (T : Tables) (ep : Episode) (G : GameDef) (seats : Nat) (moveRows : Bool) : FloatArray := Id.run do
  let size := if moveRows then fullSize else baseSize
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
    a := put a tSpots oSpots v pTiles (ofNat pay.length / 3)
    for (r, n) in pay do
      let c := pByRes + r
      a := put a tSpots oSpots v c (a.get! (oSpots + v * tSpots.width + c) + ofNat n / 6)
  a := put a tGlobal oGlobal 0 gSpots (ofNat spotCount / ofNat maxSpots)
  a := put a tGlobal oGlobal 0 gLinks (ofNat T.links.size / 300)
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

/-- What a law would change, for every seat, in the game's own seat order. It is the same for every voter, so it is
worked out once per law and turn (`Env.await`), and each voter's view reads it in its own order. -/
structure Preview where
  id : Nat
  rollsMade : Nat
  turnsTaken : Nat
  /-- Each seat's expected net at the next turn change, with the law less without it. -/
  net : Array Float
  /-- The same, by seat and row of `resources`: `seat * maxRes + row`. -/
  res : Array Float
  /-- What the law pays each seat now, if it acts at once. -/
  now : Array Float
  points : Array Float
  bank : Float
  /-- The change in each kind row's total cost. -/
  cost : Array Float
  deriving Inhabited

/-- `addEntries` for every seat at once, in the game's seat order. Each number gets the same additions in the same
order as there, so the floats are the same. -/
private def addEntriesAll (ep : Episode) (es : List Entry) (sign : Float) (net res : Array Float) :
    Array Float × Array Float :=
  es.foldl (fun (acc : Array Float × Array Float) e =>
    let amount := sign * ofNat e.amount
    let row := (ep.resRow? e.res).getD 0
    let (net, res) := acc
    let (net, res) := match e.dst with
      | .player q => (net.modify q (· + amount), res.modify (q * maxRes + row) (· + amount))
      | _ => (net, res)
    match e.src with
    | .player q => (net.modify q (· - amount), res.modify (q * maxRes + row) (· - amount))
    | _ => (net, res)) (net, res)

private def expectedTurnAll (ep : Episode) (s : State G) (sign : Float) (net res : Array Float) :
    Array Float × Array Float :=
  let rolls := Scene.rollsOf G
  let ways := rolls.foldl (fun n r => n + pips G r) 0
  rolls.foldl (fun (acc : Array Float × Array Float) r =>
    addEntriesAll ep (Engine.predictNextTurn G s r) (sign * ofNat (pips G r) / ofNat (max 1 ways)) acc.1 acc.2)
    (net, res)

/-- What this law would change, for every seat. -/
def previewOf (ep : Episode) (s : State G) (seats id : Nat) (L : Law) : Preview :=
  let s' := s.withLaw id L
  let zero (n : Nat) : Array Float := Array.replicate n 0
  let (net, res) := expectedTurnAll ep s (-1) (zero maxSeats) (zero (maxSeats * maxRes))
  let (net, res) := expectedTurnAll ep s' 1 net res
  let (now, _) := addEntriesAll ep (s.decreeEntries L) 1 (zero maxSeats) (zero (maxSeats * maxRes))
  let total (x : State G) (k : String) : Nat := (x.costOf k).foldl (fun n y => n + y.2) 0
  { id, rollsMade := s.rollsMade, turnsTaken := s.turnsTaken, net, res, now
    points := (List.range seats).toArray.map fun q => ofNat (s'.pointsOf q) - ofNat (s.pointsOf q)
    bank := ofNat s'.rules.bankRate - ofNat s.rules.bankRate
    cost := ep.rowKind.map fun k => if k == "" then 0 else ofNat (total s' k) - ofNat (total s k) }

/-- The columns of the open proposal. `pv` is its preview, if previews are on. -/
private def writeProposal (a : FloatArray) (ep : Episode) (pv : Option Preview) (s : State G) (me seats id : Nat)
    (L : Law) : FloatArray := Id.run do
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
  let some pv := pv | return a
  a := at_ a qPreviewed 1
  for i in [0:seats] do
    let q := (me + i) % seats
    a := at_ a (qNet + i) (pv.net[q]! / 4)
    a := at_ a (qNow + i) (pv.now[q]! / 4)
    a := at_ a (qPoints + i) (pv.points[q]! / 5)
  for r in [0:ep.rowRes.size] do
    a := at_ a (qMyNet + r) (pv.res[me * maxRes + r]! / 4)
  a := at_ a qBank (pv.bank / 8)
  for row in [0:maxKinds] do
    if ep.rowKind[row]! != "" then
      a := at_ a (qCost + row) (pv.cost[row]! / 8)
  return a

/-- The class of an event, as its column in the table of moves. -/
private def moveClass (rules : Rules) : Event → Nat
  | .vote _ _ yes => if yes then mVoteYes else mVoteNo
  | .move _ .endTurn => mEnd
  | .move _ (.bankTrade ..) => mBank
  | .move _ (.declare ..) => mDeclare
  | .move _ (.place k _) =>
    match (rules.piece? k).map (·.placement) with
    | some Placement.link => mLink
    | some Placement.spot => mSpot
    | some (Placement.upgrade _) => mUpgrade
    | _ => mAttach
  | _ => mEnd

/-- The table of moves: for each action on offer, what the engine says it would change. Ending the turn rolls the
dice, and a seat must not see the roll, so that row is what `predictNextTurn` gives on average over the dice. -/
private def writeMoves (a : FloatArray) (ep : Episode) (rules : Rules) (s : State G) (me seats : Nat)
    (acts : List (Nat × Event)) (held income : Array Nat) : FloatArray := Id.run do
  let mut a := a
  let w := tMoves
  let nres := ep.rowRes.size
  let probe : State G := { s with journal := [] }
  let goodsOf (h : Array Nat) (q : Nat) : Nat :=
    (List.range nres).foldl (fun n r => n + h[q * nres + r]!) 0
  let mut row := 0
  for (action, ev) in acts do
    if maxMoveRows ≤ row then
      a := put a tGlobal oGlobal 0 gOver 1
      break
    a := put a w oMoves row real 1
    a := put a w oMoves row mAction (ofNat action)
    a := put a w oMoves row (moveClass rules ev) 1
    match ev with
    | .move _ .endTurn =>
      a := put a w oMoves row mExpected 1
      let zero (n : Nat) : Array Float := Array.replicate n 0
      let (net, myRes) := expectedTurn ep s me seats 1 (zero maxSeats) (zero maxRes)
      for i in [0:seats] do
        a := put a w oMoves row (mGoods + i) (net[i]! / 10)
      for r in [0:nres] do
        a := put a w oMoves row (mMyHolding + r) (myRes[r]! / 4)
    | _ =>
      match Engine.step G probe ev with
      | .error _ => pure ()
      | .ok s' =>
        let held' := holdings ep s' seats
        for i in [0:seats] do
          let q := (me + i) % seats
          a := put a w oMoves row (mPoints + i) ((ofNat (s'.pointsOf q) - ofNat (s.pointsOf q)) / 5)
          a := put a w oMoves row (mGoods + i) ((ofNat (goodsOf held' q) - ofNat (goodsOf held q)) / 10)
        let income' := incomes ep s'.rules s' seats
        for r in [0:nres] do
          let at_ := me * nres + r
          a := put a w oMoves row (mMyHolding + r) ((ofNat held'[at_]! - ofNat held[at_]!) / 4)
          a := put a w oMoves row (mMyIncome + r) ((ofNat income'[at_]! - ofNat income[at_]!) / 6)
        if s'.phase == .ended then
          a := put a w oMoves row mEnds 1
          if s'.winner == some me then a := put a w oMoves row mWin 1
    row := row + 1
  return a

/-- The table of legal placements, in `placeOrder`. -/
private def writePlaces (a : FloatArray) (T : Tables) (ctx : Ctx G) (ep : Episode) (rules : Rules) (s : State G) (me : Nat)
    (places : Array Move) (free reach : Array Bool) (demand : Array Nat) (held income : Array Nat) : FloatArray :=
    Id.run do
  let mut a := a
  let w := tPlaces
  let nres := ep.rowRes.size
  let n := min places.size maxPlaceRows
  a := put a tGlobal oGlobal 0 gPlaces (ofNat n / ofNat maxPlaceRows)
  if places.size > maxPlaceRows then a := put a tGlobal oGlobal 0 gPlaceOver 1
  let pipsAt (v : Nat) := ctx.board.spotPips.getD v 0
  for row in [0:n] do
    let some (Move.place k loc) := places[row]? | continue
    let some e := rules.piece? k | continue
    let at_ (a : FloatArray) (c : Nat) (x : Float) := put a w oPlaces row c x
    a := at_ a real 1
    a := at_ a (match e.placement with
      | .link => plLink | .spot => plSpot | .upgrade _ => plUpgrade | .attach _ => plAttach) 1
    if let some r := ep.kindRow? k then a := at_ a (plKind + r) 1
    -- The spot the row describes: the spot itself, or the link's better free end.
    let (v, others) := match loc with
      | .spot v => (v, Option.none)
      | .link (p, q) =>
        let score (x : Nat) := (if free.getD x false then 1000 else 0) + pipsAt x
        if score q > score p then (q, some p) else (p, some q)
    a := at_ a plAt (ofNat v / ofNat maxSpots)
    if let some o := others then
      a := at_ a plAtB (ofNat o / ofNat maxSpots)
      let ends := (if free.getD v false then 1 else 0) + (if free.getD o false then 1 else 0)
      a := at_ a plFreeEnds (ofNat ends / 2)
      if reach.getD v false || reach.getD o false then a := at_ a plReach 1
    else if reach.getD v false then a := at_ a plReach 1
    let pay := ep.spotRes.getD v []
    let (x, y) := T.spotXY.getD v (0, 0)
    a := at_ a plX x
    a := at_ a plY y
    a := at_ a plPips (ofNat (pipsAt v) / 15)
    a := at_ a plGoods (ofNat (pay.map (·.1)).eraseDups.length / 3)
    let mut value := 0
    let mut fresh := 0
    for (r, n) in pay do
      value := value + n * demand[r]!
      if income[me * nres + r]! == 0 then fresh := fresh + n
    a := at_ a plDemand (ofNat value / 60)
    a := at_ a plNew (ofNat fresh / 15)
    let under : Option PieceDef := match e.placement with
      | .upgrade j => rules.piece? j
      | _ => Option.none
    let (up, uy) := match under with
      | some u => (u.points, u.yield)
      | Option.none => (0, 0)
    a := at_ a plPoints ((ofNat e.points - ofNat up) / 5)
    a := at_ a plYield ((ofNat e.yield - ofNat uy) / 3)
    let mut total := 0
    let mut short := 0
    for (r, c) in s.costOf k do
      total := total + c
      if let some col := ep.resRow? r then
        short := short + (c - min c held[me * nres + col]!)
    a := at_ a plCostTotal (ofNat total / 8)
    a := at_ a plShort (ofNat short / 8)
  return a

/-- The whole observation for the seat that must decide. `base` is the game's template. -/
def observe (T : Tables) (ep : Episode) (ctx : Ctx G) (moveRows : Bool) (base : FloatArray) (s : State G)
    (d : Decision) (places : Array Move) (free reach : Array Bool) (pv : Option Preview)
    (undo : Option (Res × Res) := Option.none) (declaredNow : List Res := []) (prune : Bool := false)
    (rankedMoves : Bool := true) : FloatArray := Id.run do
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
  -- Spots and links, from the map first, then from each piece.
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
  -- Links with no piece on them, at each end.
  let linkIdx (p q : Nat) : Option Nat :=
    match (T.linkFrom.getD p []).find? (·.1 == q) with
    | some (_, k) => some k
    | Option.none => ((T.linkFrom.getD q []).find? (·.1 == p)).map (·.2)
  let mut taken : Array Bool := Array.replicate T.links.size false
  for x in s.pieces do
    if let .link (p, q) := x.loc then
      if let some k := linkIdx p q then taken := taken.set! k true
  let mut openAt : Array Nat := Array.replicate spotCount 0
  for k in [0:T.links.size] do
    if !taken[k]! then
      let (p, q) := T.links[k]!
      openAt := (openAt.modify p (· + 1)).modify q (· + 1)
  for v in [0:spotCount] do
    a := put a tSpots oSpots v pLinksOpen (ofNat openAt[v]! / 3)
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
    | .link (p, q) =>
      linkPieces := linkPieces.modify x.owner (· + 1)
      for v in [p, q] do
        if v < maxSpots then
          let off := oSpots + v * tSpots.width
          a := a.set! (off + pLinksOf + i) (a.get! (off + pLinksOf + i) + 1 / 3)
          if i == 0 then a := a.set! (off + pLinksMine) (a.get! (off + pLinksMine) + 1 / 3)
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
  | .vote _ id L => a := writeProposal a ep pv s me seats id L
  | _ => pure ()
  -- The legal placements.
  if let .turn _ := d then
    a := writePlaces a T ctx ep rules s me places free reach demand held income
  if moveRows && !rankedMoves then
    -- The table of moves as the harness built it before `5fde545`: the legal actions in `legal`'s order (end turn,
    -- trades, declarations, placements), without the undo rule. Checkpoints trained before that commit read this.
    a := writeMoves a ep rules s me seats (legal T ep places s d) held income
  else if moveRows then
    -- The table has `maxMoveRows` rows, and a decision can have more legal actions (declarations and bank trades on
    -- worlds with many goods). So the rows come in the order that keeps what matters most: ending the turn and votes,
    -- then placements, then bank trades, then declarations. Each row names its action.
    let acts := legal T ep places s d undo prune declaredNow
    let rank : Event → Nat
      | .move _ (.place ..) => 1
      | .move _ (.bankTrade ..) => 2
      | .move _ (.declare ..) => 3
      | _ => 0
    let ordered := (List.range 4).flatMap fun k => acts.filter (rank ·.2 == k)
    a := writeMoves a ep rules s me seats ordered held income
  return a

end CharterServer.Policy
