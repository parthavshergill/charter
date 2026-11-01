import Server.Game

/-!
# Bot seats

A bot is an ordinary seat that the server plays. `candidates` lists events for the bots, best first.
The driver commits the first one that `Game.apply` accepts, so every bot action goes through
`Engine.step`. Adapted from the older game's `Server/Bots.lean`.

The policy is simple. On its own turn a bot places where the dice pay most, upgrades, builds, trades
with the bank to complete a build, and ends its turn. It votes yes on a law when the law would not
cost it resources on the next turn change and hands no other seat the win. It signs a deal that pays
it at least what it pays, and it accepts an offer that gives it at least what it gives.
-/

namespace CharterServer.Bots
open Lean Charter CharterServer.Game

variable {G : GameDef}

def botNames : List String :=
  ["Ada", "Grace", "Alan", "Emmy", "Kurt", "Hedy"]

/-- First bot name not used at the table. -/
def freshName (g : Game) : String :=
  let used := g.room.occupants.map (·.name)
  ((botNames.map (s!"Bot {·}")).find? (!used.contains ·)).getD s!"Bot {g.room.filled}"

def bal (s : State G) (p : Nat) (r : Res) : Nat := s.balance (.player p) r

/-- How often the dice pay this number. -/
def pips (G : GameDef) (n : Nat) : Nat := Scene.chanceOf G n

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

def bestBy {α : Type} (xs : List α) (f : α → Int) : Option α :=
  xs.foldl (fun b x => match b with
    | none => some x
    | some y => if f x > f y then some x else some y) none

/-- A bank trade toward paying `cost`, if trades can cover all of it. -/
def tradeToward (s : State G) (p : Nat) (cost : Bundle) (legal : List Move) : Option Move :=
  let rate := s.rules.bankRate
  let need (r : Res) : Nat := ((cost.find? (·.1 == r)).map (·.2)).getD 0
  let names := G.resources.map (·.name)
  let surplus (r : Res) : Nat := bal s p r - need r
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
      if let some m := tradeToward s p (s.costOf d.name) legal then return m
  if hasSite then
    if let some d := spotPiece G then
      if let some m := tradeToward s p (s.costOf d.name) legal then return m
  else
    if let some d := linkPiece G then
      if let some m := tradeToward s p (s.costOf d.name) legal then return m
  return .endTurn

/-- A seat's resources, after a list of entries. -/
def netFor (p : Nat) (es : List Entry) : Int :=
  es.foldl (fun acc e =>
    let gain : Int := if e.dst == .player p then e.amount else 0
    let loss : Int := if e.src == .player p then e.amount else 0
    acc + gain - loss) 0

/-- Yes if the law costs nothing at the next turn change, over every roll, and gives no other seat
the win now. -/
def lawOk (s : State G) (p id : Nat) (L : Law) : Bool :=
  let s' := s.withLaw id L
  let rolls := Scene.rollsOf G
  let total (x : State G) : Int :=
    (rolls.map fun r => (pips G r : Int) * netFor p (Engine.predictNextTurn G x r)).foldl (· + ·) 0
  let handsOthersTheWin :=
    s.turnOrder.any fun q => q != p && decide (G.targetPoints ≤ s'.pointsOf q)
  !handsOthersTheWin && decide (total s' ≥ total s)

/-- Yes if each round of the deal pays this seat at least what it pays. -/
def dealOk (p : Nat) (d : Deal) : Bool :=
  let net (ps : List Pay) : Int := ps.foldl (fun acc x =>
    let inn : Int := match x.dst with
      | .seat q => if q == p then x.amount else 0
      | .treasury => 0
    let out : Int := if x.src == p then x.amount else 0
    acc + inn - out) 0
  decide (net d.allPays ≥ 0)

def bundleTotal (b : Bundle) : Nat := (b.map (·.2)).sum

def moveEvent (p : Nat) (m : Move) : Json :=
  Json.mkObj [("t", "move"), ("seat", toJson p), ("move", moveJson m)]

/-- Candidate events for these seats, best first. `mayVote` says which laws can be voted on now. -/
def candidatesFor (g : Game) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) : List Json := Id.run do
  let some s := g.state | return []
  if bots.isEmpty || s.phase == .ended then return []
  let mut out : Array Json := #[]
  for p in s.openProposals do
    for b in bots do
      match p.body with
      | .law L =>
        if mayVote p.id && !(p.votes.any (·.1 == b)) then
          out := out.push (Json.mkObj [("t", "vote"), ("seat", toJson b), ("id", toJson p.id),
            ("yes", toJson (lawOk s b p.id L))])
      | .deal d =>
        if d.signers.contains b && !p.signed.contains b && dealOk b d then
          out := out.push (Json.mkObj [("t", "sign"), ("seat", toJson b), ("id", toJson p.id)])
  if s.phase == .actions then
    for o in s.offers do
      for b in bots do
        if o.src != b && (o.to.isNone || o.to == some b) && bundleTotal o.give ≥ bundleTotal o.get then
          out := out.push (moveEvent b (.accept o.id))
  if let some p := s.currentSeat then
    if bots.contains p then
      let legal := Engine.legalMoves g.spec.G s p
      let m := if s.phase == .setup then setupMove s legal else actionMove s p legal
      out := out.push (moveEvent p m)
      if m != .endTurn then out := out.push (moveEvent p .endTurn)
  return out.toList

/-- The first of these seats' candidates that the engine accepts. -/
def nextFor? (g : Game) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) : Option Json :=
  (candidatesFor g bots mayVote).find? fun ev => (apply g ev).toOption.isSome

/-- What the bots at this table do next. -/
def next? (g : Game) : Option Json := nextFor? g g.botSeats

end CharterServer.Bots
