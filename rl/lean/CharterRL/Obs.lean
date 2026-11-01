import CharterRL.Actions

/-!
# Observations

`template` writes what stays fixed for a game. `observe` copies it and writes the rest for one seat. Everything here
is what the game's screen shows any seat: `Engine.step` is called for the table of moves, but never for an action
that rolls the dice, and nothing reads `State.seed`. `charter-rl-check` tests that changing the seed in a state
changes no number here.

`rl/OBSERVATIONS.md` gives the meaning and scale of each column.
-/

namespace CharterRL
open Charter CharterServer CharterServer.Bots

variable {G : GameDef}

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

/-- The whole observation for the seat that must decide. `base` is the game's template. -/
def observe (T : Tables) (ep : Episode) (ctx : Ctx G) (settings : Settings) (base : FloatArray) (s : State G)
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
  | .vote _ id L => a := writeProposal a ep settings.preview s me seats id L
  | _ => pure ()
  if settings.moveRows then
    a := writeMoves a ep rules s me seats (legal T ep ctx s d) held income
  return a

end CharterRL
