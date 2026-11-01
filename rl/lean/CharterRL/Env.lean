import Lean.Data.Json
import CharterRL.Obs
import CharterRL.Gen

/-!
# The environment

One game, for any mix of seats played by the caller and seats played by strategies of the arena's pool. `reset` starts
a game and `step` applies a caller's action. Between them the environment runs everything that is not the caller's
to decide, and stops at the next decision. Every change to a game goes through `Engine.step`, here or in the arena's
`advance`.

Laws reach a table one way: at the start of a turn, by chance, `injectLaw` has the seat whose turn it is propose one
from the game's library. Seats then vote in turn order before anything else happens. A seat's vote is a decision for
the caller only under `voteMode := .policy`.
-/

namespace CharterRL
open Lean Charter CharterServer CharterServer.Bots CharterServer.Arena

/-- What `lawOk` (the hand bot's vote check) works out about one open law, for every seat at once: each seat's net
at the next turn change, summed over the rolls and weighted by how often each comes up, without the law and with it.
Only votes on this law happen while it is open, and votes do not change the next turn change, so this holds for
every voter of the law. `charter-rl-check` plays games with and without it and finds them the same. -/
structure VoteNets where
  id : Nat
  rollsMade : Nat
  turnsTaken : Nat
  before : Array Int
  after : Array Int
  deriving Inhabited

/-- A seat that the caller plays: it asks for nothing, so the arena's loop passes it by. -/
def silent : Strategy := Strategy.ofSeat "caller" fun _ _ _ => []

/-- One game in progress. -/
structure Env where
  T : Tables
  settings : Settings
  lineup : Array SeatPlan
  seed : Nat
  G : GameDef
  ctx : Ctx G
  setupTable : Arena.Table G
  playTable : Arena.Table G
  play : Play G
  ep : Episode
  /-- This game's fixed numbers, with the laws in force as of `lawsSeen`. -/
  base : FloatArray
  /-- For the chances the environment draws. It has nothing to do with the dice. -/
  draws : UInt64
  /-- The turn that has already had its chance of a law. -/
  lawTurn : Nat := 0
  lawsSeen : List Nat := []
  decision : Decision := .none
  /-- The decision's legal placements, in `placeOrder`: what the rows of `places` and actions from `actPlace` mean. -/
  places : Array Move := #[]
  /-- The decision's free spots, and the spots its seat reaches: `freeMap` and `reachMap`, worked out once. -/
  free : Array Bool := #[]
  reach : Array Bool := #[]
  /-- The last `step` was refused. -/
  refused : Bool := false
  /-- Each seat's pips when setup ended. -/
  opening : Array Nat := #[]
  pointsSeen : Array Nat := #[]
  rewards : FloatArray
  proposed : Nat := 0
  passed : Nat := 0
  decisions : Nat := 0
  /-- The current law's `VoteNets`, once a seat has voted on it. -/
  voteNets : Option VoteNets := Option.none
  /-- The open law's `Preview`, for the observations of its voters. -/
  preview : Option Preview := Option.none
  /-- Off only for the test that compares games with and without `voteNets` and a shared `preview`. -/
  shareVotes : Bool := true
  /-- Every event so far, in the server's log format, when `settings.record` is on. -/
  trail : Array Json := #[]
  /-- After each event of `trail`: the round, 1 if still in setup, the number of laws in force, and each seat's
  points. For the readable summary of a saved game. -/
  trailState : Array Json := #[]
  /-- An event had no log form, so the saved log would not replay. -/
  trailBroken : Bool := false

instance : Inhabited Env := ⟨
  { T := default, settings := {}, lineup := #[], seed := 0, G := (default : Tables).G, ctx := default,
    setupTable := default, playTable := default,
    play := Play.start (initialState (default : Tables).G 0 0 []) 0, ep := default,
    base := FloatArray.empty, draws := 0, rewards := FloatArray.empty }⟩

/-- A list of zeros, one per seat. -/
private def seatZeros : FloatArray :=
  (List.range maxSeats).foldl (fun a _ => a.push 0) FloatArray.empty

/-- The next chance. -/
private def Env.draw (e : Env) : UInt64 × Env :=
  let next := e.draws + 0x9E3779B97F4A7C15
  (scramble next, { e with draws := next })

/-- Keep this event, if the game is being recorded. A proposal's log form needs its text, which `injectLaw` gives. -/
private def Env.note (e : Env) (ev : Event) (text : Option String := Option.none) : Env :=
  if !e.settings.record then e else
  let j := match ev, text with
    | .propose seat _, some t => some (Json.mkObj [("t", "propose"), ("seat", toJson seat), ("text", t)])
    | _, _ => eventJson? ev
  let s := e.play.state
  let after := Json.arr (#[toJson s.round, toJson (if s.phase == .setup then 1 else 0), toJson s.laws.length]
    ++ (List.range e.lineup.size).toArray.map fun q => toJson (s.pointsOf q))
  match j with
  | some j => { e with trail := e.trail.push j, trailState := e.trailState.push after }
  | Option.none => { e with trailBroken := true }

/-- Who plays a seat, now. -/
private def Env.planOf (e : Env) (seat : Nat) : Option Opponent :=
  match e.lineup[seat]? with
  | some p => if e.play.state.phase == .setup then p.setup else p.play
  | none => Option.none

/-- This seat's context, under the weights of what plays it. -/
private def ctxOf {G : GameDef} (board : Board G) (o : Opponent) : Ctx G := { weights := o.weights, board }

/-- The first vote that is due: the first open law, and the first seat in turn order that has not voted and can. -/
private def nextVoter {G : GameDef} (s : State G) : Option (Nat × Nat × Law) :=
  s.openProposals.findSome? fun p =>
    match p.body with
    | .deal _ => Option.none
    | .law L =>
      (s.turnOrder.find? fun q => !(p.votes.any (·.1 == q)) && Engine.canAct s q).map (·, p.id, L)

/-- Refill the law rows when the laws in force have changed, and give a new piece its row. -/
private def Env.syncLaws (e : Env) : Env :=
  let s := e.play.state
  let ids := s.laws.map (·.1)
  if ids == e.lawsSeen then e else
  { e with
    lawsSeen := ids
    passed := e.passed + (ids.filter (!e.lawsSeen.contains ·)).length
    base := writeLaws e.base e.G s.laws
    ep := e.ep.seat s.rules.pieces }

/-- A law has a row for each new piece it makes, and a place among the laws in force. -/
private def Env.lawFits (e : Env) (L : Law) : Bool :=
  let free := (e.ep.rowKind.toList.filter (· == "")).length
  let news := L.clauses.filterMap fun | .newPiece p => some p | _ => Option.none
  e.play.state.laws.length < maxLaws && news.length ≤ free

/-- At the start of a turn in play, by chance, the seat whose turn it is proposes a law from the library. The engine
may refuse one, for example if it is already in force, so this tries each in turn from a random place. -/
private def Env.injectLaw (e : Env) : Env :=
  let s0 := e.play.state
  if e.settings.lawEvery == 0 || s0.phase != .actions || s0.turnsTaken == e.lawTurn then e else
  let e := { e with lawTurn := s0.turnsTaken }
  let (x, e) := e.draw
  let lib := e.T.library
  if x.toNat % e.settings.lawEvery != 0 || lib.isEmpty then e else
  let (y, e) := e.draw
  let s := e.play.state
  match s.currentSeat with
  | Option.none => e
  | some seat =>
    let start := y.toNat % lib.size
    let tries := (List.range lib.size).filterMap fun i => (lib[(start + i) % lib.size]?).map ((start + i) % lib.size, ·)
    let found := tries.findSome? fun (i, L) =>
      if e.lawFits L then
        match Engine.step e.G s (.propose seat (.law L)) with
        | .ok s' => some (Event.propose seat (.law L), s', i)
        | .error _ => Option.none
      else Option.none
    match found with
    | some (ev, s', i) =>
      { e with play := e.play.commit {} e.playTable ev s', proposed := e.proposed + 1 }.note ev e.T.libraryText[i]?
    | Option.none => e

/-- Record each seat's pips the first time the game is in play. -/
private def Env.noteOpening (e : Env) : Env :=
  let s := e.play.state
  if !e.opening.isEmpty || s.phase == .setup then e else
  let pipsAt (v : Nat) := e.ctx.board.spotPips.getD v 0
  let opening := s.pieces.foldl (fun acc x => match x.loc with
    | .spot v => acc.modify x.owner (· + pipsAt v)
    | .link _ => acc) (Array.replicate s.turnOrder.length 0)
  { e with opening }

/-- The strategies whose vote on a law is exactly `lawOk` under their own weights: the hand bot's family and the
champion both vote through `reactions`. -/
private def votesByLawOk (o : Opponent) : Bool :=
  ["hand", "fair", "closed", "champion", "champion-closed", "champion-ref"].contains o.name

/-- This law's `VoteNets` for this state, worked out afresh. -/
private def Env.freshNets (e : Env) (id : Nat) (L : Law) : VoteNets × Env :=
  let s := e.play.state
  let G := e.G
  let seats := s.turnOrder.length
  let rolls := Scene.rollsOf G
  let totals (x : State G) : Array Int :=
    rolls.foldl (fun acc r =>
      let es := Engine.predictNextTurn G x r
      let w : Int := pips G r
      (List.range seats).foldl (fun acc p => acc.modify p (· + w * netFor p es)) acc) (Array.replicate seats 0)
  let n : VoteNets :=
    { id, rollsMade := s.rollsMade, turnsTaken := s.turnsTaken, before := totals s, after := totals (s.withLaw id L) }
  (n, { e with voteNets := some n })

/-- This law's `VoteNets` for this state, from the cache when it is for the same law and the same turn. -/
private def Env.netsFor (e : Env) (id : Nat) (L : Law) : VoteNets × Env :=
  let s := e.play.state
  match e.voteNets with
  | some n =>
    if n.id == id && n.rollsMade == s.rollsMade && n.turnsTaken == s.turnsTaken then (n, e) else e.freshNets id L
  | Option.none => e.freshNets id L

/-- `lawOk` for this seat, from the shared nets. The same tests as `lawOk`, in the same order. -/
private def Env.lawOkShared (e : Env) (W : Weights) (seat id : Nat) (L : Law) : Bool × Env :=
  let (n, e) := e.netsFor id L
  let s := e.play.state
  let s' := s.withLaw id L
  let handsOthersTheWin := s.turnOrder.any fun q => q != seat && decide (e.G.targetPoints ≤ s'.pointsOf q)
  let endsAgainstUs := L.clauses.any Clause.isEndGame && Engine.bestSeat s' s'.turnOrder != some seat
  (!handsOthersTheWin && !endsAgainstUs && decide (n.after.getD seat 0 + W.voteMargin ≥ n.before.getD seat 0), e)

/-- Cast a vote that is not the caller's to choose, or that is the caller's under a vote mode that handles it. -/
private def Env.castVote (e : Env) (seat id : Nat) (L : Law) : Option Env :=
  let (yes, e) : Bool × Env := match e.planOf seat with
    | some o =>
      if e.shareVotes && votesByLawOk o then e.lawOkShared o.weights seat id L else
      let c := ctxOf e.ctx.board o
      let yes := (o.strategy.decide c e.play.state [seat]).findSome? fun
        | .vote q i y => if q == seat && i == id then some y else Option.none
        | _ => Option.none
      (yes.getD false, e)
    | Option.none =>
      match e.settings.voteMode with
      | .bot => if e.shareVotes then e.lawOkShared e.ctx.weights seat id L else (lawOk e.ctx e.play.state seat id L, e)
      | _ =>
        let (x, e) := e.draw
        (x % 2 == 0, e)
  let s := e.play.state
  match Engine.step e.G s (.vote seat id yes) with
  | .ok s' => some ({ e with play := e.play.commit {} e.playTable (.vote seat id yes) s' }.note (.vote seat id yes))
  | .error _ =>
    match Engine.step e.G s (.vote seat id false) with
    | .ok s' => some ({ e with play := e.play.commit {} e.playTable (.vote seat id false) s' }.note (.vote seat id false))
    | .error _ => Option.none

/-- Wait for this decision, and work out its placements once. -/
def Env.await (e : Env) (d : Decision) : Env :=
  let s := e.play.state
  match d with
  | .turn seat =>
    let free := freeMap e.ctx s
    let reach := reachMap e.ctx s seat
    { e with decision := d, places := placeList e.ctx e.ep s seat free reach, free, reach }
  | .vote seat id L =>
    let cached := match e.preview with
      | some p => if e.shareVotes && p.id == id && p.rollsMade == s.rollsMade && p.turnsTaken == s.turnsTaken then some p
        else Option.none
      | Option.none => Option.none
    let preview := if !e.settings.preview then Option.none else
      match cached with
      | some p => some p
      | Option.none => some (previewOf e.ep s s.turnOrder.length id L)
    { e with decision := d, places := #[], free := freeMap e.ctx s, reach := reachMap e.ctx s seat, preview }
  | .none => { e with decision := d, places := #[], free := #[], reach := #[] }

/-- Run until a caller must decide or the game ends. A law passing is counted in `syncLaws`, by a new id appearing
among the laws in force. -/
private def Env.settle (e : Env) : Nat → Env
  | 0 => { e with decision := .none }
  | fuel + 1 =>
    let e := e.syncLaws
    let s := e.play.state
    if s.phase == .ended then { e with decision := .none } else
    let e := e.injectLaw
    let e := e.noteOpening
    let s := e.play.state
    if s.phase == .ended then { e with decision := .none } else
    match nextVoter s with
    | some (seat, id, L) =>
      let callerDecides := (e.planOf seat).isNone && e.settings.voteMode == .policy
      if callerDecides then e.await (.vote seat id L) else
      match e.castVote seat id L with
      | some e' => Env.settle e' fuel
      | Option.none => { e with decision := .none }
    | Option.none =>
      match s.currentSeat with
      | Option.none => { e with decision := .none }
      | some seat =>
        if (e.planOf seat).isNone then e.await (.turn seat) else
        let table := if s.phase == .setup then e.setupTable else e.playTable
        match advance {} table e.play with
        | some (ev, p) => Env.settle ({ e with play := p }.note ev) fuel
        | Option.none => { e with decision := .none }

/-- How many events a game can have, including those the environment adds. -/
private def Env.fuel (e : Env) : Nat := eventCap e.G e.lineup.size + 1000

/-- The reward of each seat when the game is over: for winning, and for its place, with the winner first and then by
points and turn order. -/
private def Env.finalRewards (e : Env) : FloatArray := Id.run do
  let s := e.play.state
  let seats := s.turnOrder.length
  let key (q : Nat) : Nat := (if s.winner == some q then 100000 else 0) + s.pointsOf q * 10 + (maxSeats - q)
  let order := (s.turnOrder.toArray.qsort fun a b => key a > key b).toList
  let mut out := seatZeros
  for (q, rank) in order.zipIdx do
    let standing := 1 - 2 * Float.ofNat rank / Float.ofNat (max 1 (seats - 1))
    let win := if s.winner == some q then e.settings.rewardWin else 0
    out := out.set! q (win + e.settings.rewardStanding * standing)
  return out

/-- Work out the rewards since the last action. -/
private def Env.reckon (e : Env) : Env := Id.run do
  let s := e.play.state
  let mut rewards := seatZeros
  let mut e := e
  if e.settings.shapingPoints != 0 then
    let now := (List.range s.turnOrder.length).toArray.map s.pointsOf
    for q in [0:now.size] do
      let gained := Float.ofNat now[q]! - Float.ofNat (e.pointsSeen.getD q 0)
      rewards := rewards.set! q (e.settings.shapingPoints * gained / Float.ofNat (max 1 e.G.targetPoints))
    e := { e with pointsSeen := now }
  if s.phase == .ended then
    let final := e.finalRewards
    for q in [0:maxSeats] do
      rewards := rewards.set! q (rewards.get! q + final.get! q)
  return { e with rewards }

/-- Start a game with this seed. The map, the dice, the row order and the laws all follow from the seed. -/
def Env.start (T : Tables) (settings : Settings) (lineup : Array SeatPlan) (seed : Nat) (shareVotes : Bool := true) :
    Except String Env := do
  let T := if settings.declareAlways then { T with declares := true } else T
  let seats := lineup.size
  let G := if settings.randomMap then randomMap T.G seed else T.G
  if settings.randomMap && !G.shapeChecks then
    throw s!"a random map of {T.id} failed the game's checks, with seed {seed}"
  let board : Board G := if settings.randomMap then Board.remap G T else { T.board with }
  let ep := Episode.make G settings.slotOrder seed
  let names := (G.resources.map (·.name)).toArray
  let planFor (pick : SeatPlan → Option Opponent) : Arena.Table G :=
    { plans := lineup.map fun p => match pick p with
        | some o => (o.strategy, ctxOf board o)
        | Option.none => (silent, { weights := .default, board })
      names }
  let s := startOf G seats seed
  let e : Env :=
    { T, settings, lineup, seed, G, ctx := { weights := .default, board }
      setupTable := planFor (·.setup), playTable := planFor (·.play)
      play := Play.start s seats, ep
      base := template T ep G seats settings.moveRows
      draws := mix seed 77, lawsSeen := s.laws.map (·.1)
      pointsSeen := Array.replicate seats 0, rewards := seatZeros, shareVotes }
  return (Env.settle e e.fuel).reckon

/-- Apply an action for the seat that must decide. An action not on offer, or one the engine refuses, changes nothing
and sets `refused`. -/
def Env.step (e : Env) (action : Nat) : Env :=
  let bad := { e with refused := true, rewards := seatZeros }
  match decode e.T e.ep e.places e.decision action with
  | Option.none => bad
  | some ev =>
    match Engine.step e.G e.play.state ev with
    | .error _ => bad
    | .ok s' =>
      let table := if e.play.state.phase == .setup then e.setupTable else e.playTable
      let e' := ({ e with
        play := e.play.commit {} table ev s'
        refused := false
        decisions := e.decisions + 1 } : Env).note ev
      (Env.settle e' e'.fuel).reckon

/-- The numbers for the seat that must decide. -/
def Env.observation (e : Env) : FloatArray :=
  observe e.T e.ep e.ctx e.settings e.base e.play.state e.decision e.places e.free e.reach e.preview

/-- The actions on offer. -/
def Env.legalActions (e : Env) : List (Nat × Event) := legal e.T e.ep e.places e.play.state e.decision

def Env.mask (e : Env) : ByteArray := maskOf e.legalActions

/-- What this named strategy would do now, as an action. `none` if it wants something with no action, such as an
offer, or there is no decision. -/
def Env.suggest (e : Env) (name : String) : Option Nat := do
  let o ← opponents.find? (·.name == name)
  let seat ← e.decision.seat?
  let s := e.play.state
  let wants := (o.strategy.decide (ctxOf e.ctx.board o) s [seat]).filter (seatOf · == some seat)
  match e.decision with
  | .vote _ id _ =>
    wants.findSome? fun
      | .vote _ i yes => if i == id then some (if yes then actVoteYes else actVoteNo) else Option.none
      | _ => Option.none
  | _ =>
    let moves := wants.filter fun | .move .. => true | _ => false
    let (chosen : Event) ← (moves.find? fun ev => (Engine.step e.G s ev).toOption.isSome)
    encode e.ep e.places e.decision chosen

/-! ## The game as a server log

`make spectate` replays a folder of server logs. This is one game's log, one JSON event per line: the table's
creation, with the seed the dice come from and the dealt map, a join per seat with its nonce, the start, and then
every event of the game. The server's `Game.create` and `Game.apply` replay it through `Engine.step` from the same
start as `startOf`. `names` names the seats. -/

/-- The game so far as a server log, or why it cannot be one. -/
def Env.savedLog (e : Env) (code : String) (names : List String) : Except String String := do
  if !e.settings.record then throw "this game was not recorded: set record to true"
  if e.trailBroken then throw "an event of this game has no log form"
  let seats := e.lineup.size
  let deal := e.G.map.regions.map fun r => (r.res, r.number)
  let create := Json.mkObj
    [ ("t", "create"), ("code", code), ("seats", toJson seats), ("game", e.T.id)
    , ("_serverSeed", toJson (Arena.derive e.seed 0)), ("_map", toJson deal), ("_rlSeed", toJson e.seed) ]
  let joins := (List.range seats).map fun i =>
    Json.mkObj
      [ ("t", "join"), ("name", names.getD i s!"Seat {i}"), ("kind", "bot")
      , ("_token", toString (Arena.derive e.seed (100 + i))), ("nonce", toJson (Arena.derive e.seed (200 + i))) ]
  let lines := [create] ++ joins ++ [Json.mkObj [("t", "start")]] ++ e.trail.toList
  return "\n".intercalate (lines.map (·.compress)) ++ "\n"

/-- After each event of the saved log: `[round, setup, laws in force, points of seat 0, 1, ...]`, one line each. -/
def Env.savedState (e : Env) : String :=
  "\n".intercalate (e.trailState.toList.map (·.compress)) ++ "\n"

/-! ## Numbers about a game, for the caller. `infoNames` is their order. -/

def infoNames : List String :=
  [ "over", "winner", "round", "events", "rejected", "proposed", "passed", "decisions", "offers" ]
  ++ (List.range maxSeats).map (s!"points{·}") ++ (List.range maxSeats).map (s!"opening{·}")

def Env.info (e : Env) : FloatArray :=
  let s := e.play.state
  let seat (f : Nat → Nat) := (List.range maxSeats).map fun q =>
    if q < s.turnOrder.length then Float.ofNat (f q) else 0
  let first : List Float :=
    [ if s.phase == .ended then 1 else 0
    , match s.winner with | some w => Float.ofNat w | Option.none => -1
    , Float.ofNat s.round, Float.ofNat e.play.events, Float.ofNat e.play.rejected
    , Float.ofNat e.proposed, Float.ofNat e.passed, Float.ofNat e.decisions
    , Float.ofNat (e.play.offersMade.foldl (· + ·) 0) ]
  (first ++ seat s.pointsOf ++ seat (e.opening.getD · 0)).foldl FloatArray.push FloatArray.empty

/-! ## Reading a configuration -/

private def jGet (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

private def readFloat (j : Json) (k : String) (dflt : Float) : Except String Float :=
  match jGet j k with
  | Option.none => pure dflt
  | some v =>
    match v.getNum? with
    | .ok n => pure n.toFloat
    | .error _ => throw s!"{k} must be a number"

private def readBool (j : Json) (k : String) (dflt : Bool) : Except String Bool :=
  match jGet j k with
  | Option.none => pure dflt
  | some v =>
    match v.getBool? with
    | .ok b => pure b
    | .error _ => throw s!"{k} must be true or false"

/-- The settings of a configuration. An unknown key is an error, so a misspelt switch cannot pass unnoticed. -/
def readSettings (j : Json) : Except String Settings := do
  let known := ["game", "seats", "lineup", "seed", "law_every", "vote_mode", "move_rows", "preview", "random_map",
    "slot_order", "reward_win", "reward_standing", "shaping_points", "record", "declare_always"]
  match j.getObj? with
  | .error _ => throw "a configuration must be an object"
  | .ok kvs =>
    for (k, _) in kvs.toList do
      if !known.contains k then throw s!"there is no setting called {k}"
  let d : Settings := {}
  let lawEvery ← match jGet j "law_every" with
    | Option.none => pure d.lawEvery
    | some v => match v.getNat? with
      | .ok n => pure n
      | .error _ => throw "law_every must be a whole number"
  let voteMode ← match jGet j "vote_mode" with
    | Option.none => pure d.voteMode
    | some v => match v.getStr? with
      | .ok "random" => pure .random
      | .ok "bot" => pure .bot
      | .ok "policy" => pure .policy
      | _ => throw "vote_mode must be random, bot or policy"
  let slotOrder ← match jGet j "slot_order" with
    | Option.none => pure d.slotOrder
    | some v => match v.getStr? with
      | .ok "shuffled" => pure .shuffled
      | .ok "game" => pure .game
      | _ => throw "slot_order must be shuffled or game"
  pure
    { lawEvery, voteMode, slotOrder
      moveRows := ← readBool j "move_rows" d.moveRows
      preview := ← readBool j "preview" d.preview
      randomMap := ← readBool j "random_map" d.randomMap
      rewardWin := ← readFloat j "reward_win" d.rewardWin
      rewardStanding := ← readFloat j "reward_standing" d.rewardStanding
      shapingPoints := ← readFloat j "shaping_points" d.shapingPoints
      record := ← readBool j "record" d.record
      declareAlways := ← readBool j "declare_always" d.declareAlways }

/-- One seat of a lineup: `caller`, a strategy's name, or `first+then` for one thing in setup and another after. -/
def readSeat (text : String) : Except String SeatPlan := do
  let one (name : String) : Except String (Option Opponent) :=
    if name == "caller" then pure Option.none
    else match opponents.find? (·.name == name) with
      | some o => pure (some o)
      | Option.none => throw s!"there is no strategy called {name}. There are {opponents.map (·.name)}"
  match text.splitOn "+" with
  | [a] =>
    let o ← one a
    pure { setup := o, play := o }
  | [a, b] => pure { setup := ← one a, play := ← one b }
  | _ => throw s!"a seat cannot be {text}"

/-- A new game from a configuration. -/
def Env.ofJson (j : Json) : Except String Env := do
  let settings ← readSettings j
  let id ← j.getObjValAs? String "game"
  let T ← match tablesOf? id, Gen.tables? id with
    | some T, _ => pure T
    | none, some made => made
    | none, none => throw s!"there is no game called {id}"
  let lineup ← j.getObjValAs? (List String) "lineup"
  let seats := lineup.length
  if seats < T.minSeats || T.maxSeats < seats then
    throw s!"{id} has {T.minSeats} to {T.maxSeats} seats, and this lineup has {seats}"
  match T.problems with
  | [] => pure ()
  | ps => throw s!"{id} does not fit the layout: {ps}"
  let plans ← lineup.mapM readSeat
  let seed := match jGet j "seed" with
    | some v => (v.getNat?.toOption).getD 1
    | Option.none => 1
  Env.start T settings plans.toArray seed

end CharterRL
