import Server.ArenaPlay

/-!
# The bot as it was, for checking

This is the policy without the shortcuts of `Server/BotCore.lean`: it asks
`Engine.legalMoves` for every decision, at about 90 calls of `step` each. It does not play at real
tables. `charter-arena --check-reference` plays games and checks at every step that the fast policy chooses
what this one chooses, including with laws and deals in force.
-/

namespace CharterServer.Reference
open Lean Charter CharterServer CharterServer.Bots CharterServer.Arena

variable {G : GameDef}

/-- What a spot is worth: 10 per pip, and 5 per resource it touches. -/
def spotValue (G : GameDef) (v : Nat) : Nat :=
  let rs := (paidRegions G).filter (·.spots.contains v)
  (rs.map fun r => 10 * pips G r.number).sum + 5 * (rs.map (·.res)).eraseDups.length

def isFree (s : State G) (v : Nat) : Bool :=
  (s.pieceAt v).isNone && (s.neighbours v).all fun w => (s.pieceAt w).isNone

def freeSites (s : State G) : List Nat := (List.range G.map.spotCount).filter (isFree s)

/-- The spots at most `steps` links from a spot. -/
def ball (s : State G) (v : Nat) : Nat → List Nat
  | 0 => [v]
  | k + 1 => ((ball s v k).flatMap fun w => w :: s.neighbours w).eraseDups

/-- A road is worth the best free site near its ends, less for each step away. -/
def roadValue (s : State G) (l : Nat × Nat) : Int :=
  let sites := freeSites s
  let near (d : Nat) : List Nat :=
    (ball s l.1 d ++ ball s l.2 d).filter sites.contains
  let at_ (d : Nat) : Int :=
    (((near d).map (fun v => (spotValue G v : Int))).foldl max 0) - 40 * d
  [0, 1, 2, 3].foldl (fun b d => if (near d).isEmpty then b else max b (at_ d)) (-100)

/-- The points one unit of a good is worth now. -/
def worthOf (s : State G) (r : Res) : Nat :=
  (s.rules.worth.filter (·.1 == r)).foldl (fun n x => n + x.2) 0

/-- The points some goods are worth now. -/
def goodsWorth (s : State G) (b : Bundle) : Nat :=
  b.foldl (fun n x => n + x.2 * worthOf s x.1) 0

/-- The points a piece of this kind is worth now. -/
def pointsOfKind (s : State G) (k : PieceKind) : Nat :=
  (((s.rules.pieces.filter (·.name == k)).head?).map (·.points)).getD 0

/-- A bank trade toward building `k`, if trades can cover all of its cost. A good worth points is never
spare, unless the piece is worth more points than its cost and the goods given for one trade. -/
def tradeToward (s : State G) (p : Nat) (k : PieceKind) (legal : List Move) : Option Move :=
  let cost := s.costOf k
  let rate := s.rules.bankRate
  let need (r : Res) : Nat := ((cost.find? (·.1 == r)).map (·.2)).getD 0
  let names := G.resources.map (·.name)
  let kept (r : Res) : Bool :=
    worthOf s r > 0 && !(goodsWorth s cost + rate * worthOf s r < pointsOfKind s k)
  let surplus (r : Res) : Nat := if kept r then 0 else bal s p r - need r
  let short := names.filter fun r => need r > bal s p r
  let missing := (short.map fun r => need r - bal s p r).sum
  if missing == 0 || rate == 0 then none else
  if (names.map fun r => surplus r / rate).sum < missing then none else
  match short.head?, bestBy (names.filter fun r => surplus r ≥ rate) (fun r => (surplus r : Int)) with
  | some m, some g =>
    let mv := Move.bankTrade g m
    if legal.contains mv then some mv else none
  | _, _ => none

/-- The setup move: the best spot, then the road toward the best site. -/
def setupMove (s : State G) (legal : List Move) : Move :=
  let spotMoves := legal.filterMap fun m => match m with
    | .place _ (.spot v) => some (m, (spotValue G v : Int))
    | _ => none
  match bestBy spotMoves (·.2) with
  | some (m, _) => m
  | none =>
    let roads := legal.filterMap fun m => match m with
      | .place _ (.link l) => some (m, roadValue s l)
      | _ => none
    match bestBy roads (·.2) with
    | some (m, _) => m
    | none => .endTurn

/-- The kind of placement a move makes under the rules in force. -/
def placementOf (s : State G) : Move → Option Placement
  | .place k _ => (s.rules.piece? k).map (·.placement)
  | _ => none

/-- The move on a bot's turn: upgrade, settle, law-made piece, road, trade, end. -/
def actionMove (s : State G) (p : Nat) (legal : List Move) : Move := Id.run do
  let places (test : Placement → Bool) : List Move :=
    legal.filter fun m => match placementOf s m with
      | some pl => test pl
      | none => false
  let spotOf (m : Move) : Int := match m with
    | .place _ (.spot v) => spotValue G v
    | _ => 0
  if let some m := bestBy (places fun | .upgrade _ => true | _ => false) spotOf then return m
  if let some m := bestBy (places fun | .spot => true | _ => false) spotOf then return m
  if let some m := (places fun | .attach _ => true | _ => false).head? then return m
  let hasSite := (freeSites s).any (s.reaches p)
  if !hasSite then
    let roads := (places fun | .link => true | _ => false).filterMap fun m => match m with
      | .place _ (.link l) => some (m, roadValue s l)
      | _ => none
    if let some (m, _) := bestBy roads (·.2) then return m
  if let some (d, old) := upgradePiece G then
    if s.countOf p old > 0 && (s.rules.piece? d.name).isSome then
      if let some m := tradeToward s p d.name legal then return m
  if hasSite then
    if let some d := spotPiece G then
      if let some m := tradeToward s p d.name legal then return m
  else
    if let some d := linkPiece G then
      if let some m := tradeToward s p d.name legal then return m
  return .endTurn

/-- Yes if the law costs nothing at the next turn change, over every roll, and gives no other seat
the win now. -/
def lawOk (s : State G) (p id : Nat) (L : Law) : Bool :=
  let s' := s.withLaw id L
  let rolls := Scene.rollsOf G
  let total (x : State G) : Int :=
    (rolls.map fun r => (pips G r : Int) * netFor p (Engine.predictNextTurn G x r)).foldl (· + ·) 0
  let handsOthersTheWin :=
    s.turnOrder.any fun q => q != p && decide (G.targetPoints ≤ s'.pointsOf q)
  let endsAgainstUs := L.clauses.any Clause.isEndGame && Engine.bestSeat s' s'.turnOrder != some p
  !handsOthersTheWin && !endsAgainstUs && decide (total s' ≥ total s)

/-- Yes if each round of the deal pays this seat at least what it pays. -/
def dealOk (p : Nat) (d : Deal) : Bool :=
  let net (ps : List Pay) : Int := ps.foldl (fun acc x =>
    let inn : Int := match x.dst with
      | .seat q => if q == p then x.amount else 0
      | .treasury => 0
    let out : Int := if x.src == p then x.amount else 0
    acc + inn - out) 0
  decide (net d.allPays ≥ 0)

/-- Candidate events for these seats, best first. -/
def candidates (s : State G) (bots : List Nat) : List Event := Id.run do
  if bots.isEmpty || s.phase == .ended then return []
  let mut out : Array Event := #[]
  for p in s.openProposals do
    for b in bots do
      match p.body with
      | .law L =>
        if !(p.votes.any (·.1 == b)) then
          out := out.push (.vote b p.id (lawOk s b p.id L))
      | .deal d =>
        if d.signers.contains b && !p.signed.contains b && dealOk b d then
          out := out.push (.sign b p.id)
  if s.phase == .actions then
    for o in s.offers do
      for b in bots do
        if o.src != b && (o.to.isNone || o.to == some b) &&
            bundleTotal o.give + 100 * goodsWorth s o.give ≥ bundleTotal o.get + 100 * goodsWorth s o.get then
          out := out.push (.move b (.accept o.id))
  if let some p := s.currentSeat then
    if bots.contains p then
      let legal := Engine.legalMoves G s p
      let m := if s.phase == .setup then setupMove s legal else actionMove s p legal
      out := out.push (.move p m)
      if m != .endTurn then out := out.push (.move p .endTurn)
  return out.toList

/-- The bot as it was, as a strategy. Its weights are ignored. -/
def strategy : Strategy :=
  { name := "hand-reference", decide := fun _ s bots => candidates s bots }

/-! ## Comparing the two -/

/-- Events in the log's form, to compare them. -/
def shown (es : List Event) : List String :=
  es.map fun e => ((eventJson? e).map (·.compress)).getD "other"

/-- Laws to put in force during a check: higher and lower prices, a new bank rate, law-made pieces, laws
that take resources on a build or a roll, and goods worth points. They name this game's own goods and pieces. -/
def testLaws (G : GameDef) : List Law :=
  let goods := goodsOf G
  let r0 := goods.getD 0 ""
  let r1 := goods.getD 1 ""
  let r2 := goods.getD 2 ""
  let spot := ((spotPiece G).map (·.name)).getD ""
  let link := ((linkPiece G).map (·.name)).getD ""
  let up := match upgradePiece G with
    | some (d, _) => d.name
    | none => spot
  [ { title := "Dear spots", clauses := [.setCost spot [(r0, 2), (r1, 1)]] }
  , { title := "Rate 2", clauses := [.setBankRate 2] }
  , { title := "Granary"
      clauses := [.newPiece { name := "granary", cost := [(r0, 1)], points := 1
                              placement := .attach spot, yield := 1, limit := 2 }] }
  , { title := "Tower"
      clauses := [.newPiece { name := "tower", cost := [(r1, 1), (r2, 1)], points := 3
                              placement := .upgrade spot, yield := 1, limit := 2 }] }
  , { title := "Road toll"
      clauses := [.onBuild link [.transfer .actor .treasury (.lit r1) (.lit 2)]] }
  , { title := "A roll taxes"
      clauses := [.onRoll [.forEach .yes [.transfer .each .bank (.lit r0) (.lit 1)]]] }
  , { title := "Cheap upgrades", clauses := [.setCost up [(r2, 1)]] }
  , { title := "Rate 0", clauses := [.setBankRate 0] }
  , { title := "A good is worth points", clauses := [.setWorth r1 1, .setWorth r2 2] } ]

/-- A deal that forbids a seat to build on half the map, to put in force during a check. -/
def testDeal (G : GameDef) (seat id round : Nat) : ActiveDeal :=
  let spot := ((spotPiece G).map (·.name)).getD ""
  let link := ((linkPiece G).map (·.name)).getD ""
  { id, lastRound := round + 3, startRound := round, builtBefore := 0
    deal :=
      { title := "Stay away", signers := [seat], rounds := 4, exitNotice := 0, deposits := []
        terms :=
          [ .noBuild seat spot ((List.range G.map.spotCount).filter (· % 2 == 0))
          , .noBuild seat link ((List.range G.map.spotCount).filter (· % 3 == 0)) ] } }

/-- What a check saw. -/
structure Seen where
  states : Nat := 0
  decisions : Nat := 0
  withLaws : Nat := 0
  withDeals : Nat := 0
  withOffers : Nat := 0
  withVotes : Nat := 0
  places : Nat := 0
  trades : Nat := 0
  finished : Nat := 0
  deriving Inhabited

/-- Compare the two bots for every seat at this state. Gives the first difference. -/
def compareAt (ctx : Ctx G) (s : State G) : Option String :=
  s.turnOrder.findSome? fun seat =>
    let fast := shown (handEvents ctx s [seat])
    let slow := shown (candidates s [seat])
    if fast == slow then none
    else some s!"seat {seat}, round {s.round}, phase {repr s.phase}: fast {fast}, reference {slow}"

/-- How often a check changes the laws, or offers one to a vote. -/
inductive Scenario where
  /-- The game as it is. -/
  | plain
  /-- Laws go in force as the game goes on, and some are put to a vote. -/
  | laws
  /-- A deal forbids builds. -/
  | deals
  deriving Inhabited, BEq

/-- The state after a check's change to it, for this many events so far. -/
def stir (scenario : Scenario) (s : State G) (n : Nat) : State G :=
  match scenario with
  | .plain => s
  | .laws =>
    if n % 37 == 36 && s.phase == .actions then
      let ls := testLaws G
      match ls[(n / 37) % ls.length]? with
      | some L => s.withLaw (1000 + n) L
      | none => s
    else s
  | .deals =>
    if s.deals.isEmpty && s.phase == .actions then
      match s.currentSeat with
      | some seat => { s with deals := [testDeal G seat s.dealsStarted s.round] }
      | none => s
    else s

/-- Play a game, comparing the two bots at every step. Gives what it saw, or the first difference. -/
def checkGame (scenario : Scenario) (t : Table G) (seed : Nat) (seen : Seen) : Except String Seen := Id.run do
  let seats := t.plans.size
  let ctx : Ctx G := match t.plans[0]? with
    | some (_, c) => { c with weights := .default }
    | none => Ctx.of G
  let mut p := Play.start (startOf G seats seed) seats
  let mut seen := seen
  for n in [0:eventCap G seats] do
    if p.state.phase == .ended then
      seen := { seen with finished := seen.finished + 1 }
      break
    let s := stir scenario p.state n
    -- Now and then the current seat puts a law to the vote.
    let s := if scenario == .laws && n % 53 == 52 then
        match s.currentSeat, (testLaws G)[(n / 53) % (testLaws G).length]? with
        | some seat, some L =>
          match Engine.step G s (.propose seat (.law L)) with
          | .ok s' => s'
          | .error _ => s
        | _, _ => s
      else s
    p := { p with state := s }
    if let some why := compareAt ctx s then
      return .error s!"seed {seed}, event {n}: {why}"
    seen := { seen with
      states := seen.states + 1
      decisions := seen.decisions + seats
      withLaws := seen.withLaws + (if s.laws.isEmpty then 0 else 1)
      withDeals := seen.withDeals + (if s.deals.isEmpty then 0 else 1)
      withOffers := seen.withOffers + (if s.offers.isEmpty then 0 else 1)
      withVotes := seen.withVotes + (if s.openProposals.isEmpty then 0 else 1) }
    match advance {} t p with
    | none => break
    | some (e, p') =>
      p := p'
      match e with
      | .move _ (.place ..) => seen := { seen with places := seen.places + 1 }
      | .move _ (.bankTrade ..) => seen := { seen with trades := seen.trades + 1 }
      | _ => pure ()
  return .ok seen

end CharterServer.Reference
