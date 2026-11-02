import Server.Game
import Server.Policy.Obs
import Server.Policy.Net

/-!
# The trained policy as a bot

`CHARTER_BOT=policy` makes every bot seat play by the trained network in the weights file
`CHARTER_POLICY_WEIGHTS` (default `Server/Policy/policy.chpw`). Without it, bot seats play the rule-based bot of
`Server/BotCore.lean`, as before.

How one decision is made:

1. On its own turn, the seat builds the observation (`observe`) and the list of actions the engine accepts now
   (`legal`, each one asked of the engine). The network scores every action. The seat picks the legal action with
   the highest score. Ties go to the lowest action number. No sampling, so the same state gives the same move.
2. Votes, signatures and accepted offers use the rule-based bot's code, as before. The checkpoints were trained
   with the harness's `vote_mode=bot`, so the network never learned to vote, and it has no action for deals or
   offers.
3. The event goes to the driver, which commits it through `Game.apply` and so through `Engine.step`, like every
   other bot event.

There is no fallback inside this path. Layout 2's limits are the engine's own, so every game that passes `G.Valid`
fits. `problems` would refuse a game past them when the bot joins, with the reason.

Each seat's recurrent state starts at zero each game and moves between its own decisions by the weights file's
state rule (`StateRule`: carried, set to 0.5 at each turn start, or zero), which must match how the checkpoint
was trained. The driver moves it on after each of the seat's moves goes through.
-/

namespace CharterServer.Policy
open Lean Charter CharterServer CharterServer.Game CharterServer.Bots

variable {G : GameDef}

/-- Is the policy bot on: `CHARTER_BOT=policy`. Read once when the server starts. -/
initialize policyOn : Bool ← do
  return (← IO.getEnv "CHARTER_BOT") == some "policy"

/-- Where the weights file is. -/
def weightsPath : IO System.FilePath := do
  return (← IO.getEnv "CHARTER_POLICY_WEIGHTS").getD "Server/Policy/policy.chpw"

/-- Read and check a weights file for this layout. -/
def loadNet (path : System.FilePath) : IO (Except String Net) := do
  let bytes ← try IO.FS.readBinFile path catch e => return .error s!"cannot read {path}: {e}"
  match Net.read bytes with
  | .error e => return .error s!"{path}: {e}"
  | .ok n =>
    if n.layoutVersion != version then
      return .error s!"{path}: layout version {n.layoutVersion}, and this server reads version {version}"
    if n.obsSize != baseSize || (n.actSize != actSize && n.actSize != actSize + 1) then
      return .error s!"{path}: observation {n.obsSize} and actions {n.actSize}, expected {baseSize} and {actSize} (or one more, for the no-op)"
    return .ok n

/-- The network, loaded once when the server starts, if the policy bot is on. -/
initialize policyNet : Except String Net ← do
  if !policyOn then return .error "the policy bot is off (CHARTER_BOT is not policy)"
  loadNet (← weightsPath)

/-- What the network sees of this game. -/
def tablesOf (g : Game) : Tables :=
  Tables.make g.spec.G (g.spec.layout.spots.map (·.toPixel 1.0))

/-- Why the network cannot play this game, if it cannot. Layout 2's limits are the engine's own
(`Charter.maxResources` and the rest), so a game that passes `G.Valid` always fits and this is empty. It is kept
so that a checkpoint with a smaller layout could never play a game it does not fit. -/
def problems (g : Game) : List String :=
  let G := g.spec.G
  (if G.resources.length ≤ maxRes then [] else [s!"{G.resources.length} resources, and the limit is {maxRes}"]) ++
  (if G.pieces.length ≤ maxKinds then [] else [s!"{G.pieces.length} kinds of piece, and the limit is {maxKinds}"]) ++
  (if G.map.spotCount ≤ maxSpots then [] else [s!"{G.map.spotCount} spots, and the limit is {maxSpots}"]) ++
  (if G.foundingLaws.length ≤ maxLaws then [] else [s!"{G.foundingLaws.length} founding laws, and the limit is {maxLaws}"])

/-- Everything one turn decision needs: the observation, and the legal actions with their events. -/
def decisionFor (g : Game) (s : State g.spec.G) (seat : Nat) : FloatArray × List (Nat × Event) :=
  let G := g.spec.G
  let T := tablesOf g
  let ep := (Episode.make G).seat s.rules.pieces
  let ctx := Ctx.of G
  let d : Decision := .turn seat
  let free := freeMap ctx s
  let reach := reachMap ctx s seat
  let places := placeList ctx ep s seat free reach
  let obs := observe T ep ctx (template T ep G s.turnOrder.length) s d places free reach none
  (obs, legal T ep places s d)

/-- The observation this seat sees on its turn, as the network reads it. -/
def observationFor (g : Game) (s : State g.spec.G) (seat : Nat) : FloatArray := (decisionFor g s seat).1

/-- The network's move for this seat on its turn, starting from recurrent state `state`: the event, how many
actions were legal, and the new state. `none` when it is not this seat's turn. -/
def turnEventFrom (net : Net) (state : Array FloatArray) (g : Game) (s : State g.spec.G) (seat : Nat) :
    Except String (Option (Event × Nat × Array FloatArray)) := do
  if s.currentSeat != some seat || s.phase == .ended then return none
  let (obs, acts) := decisionFor g s seat
  if acts.isEmpty then
    throw s!"seat {seat} has its turn and no legal action has a number in the layout"
  let (logits, state') ← net.forward obs state
  let some a := net.best logits (acts.map (·.1)).toArray
    | throw "no legal action was scored"
  match acts.find? (·.1 == a) with
  | some (_, ev) => return some (ev, acts.length, state')
  | none => throw s!"action {a} has no event"

/-- The network's move for this seat on its turn, from a zero recurrent state, as the server plays it. -/
def turnEvent (net : Net) (g : Game) (s : State g.spec.G) (seat : Nat) : Except String (Option (Event × Nat)) := do
  return (← turnEventFrom net net.initState g s seat).map fun (ev, n, _) => (ev, n)

/-- Is this event a reaction (a vote, a signature or an accepted offer), not a move on the seat's turn? -/
def isReactionJson (ev : Json) : Bool :=
  match jStr ev "t" with
  | some "vote" | some "sign" => true
  | some "move" => (jField ev "move").bind (jStr · "t") == some "accept"
  | _ => false

/-- Each policy seat's recurrent state after its last move that went through, and the turn it was in
(`State.turnsTaken`). A seat not here starts from zero. -/
abbrev Memory := Std.HashMap Nat (Nat × Array FloatArray)

/-- The state this seat decides from now, by the weights file's state rule: carried, set at a new turn, or zero. -/
def Memory.stateOf (mem : Memory) (net : Net) (s : State G) (seat : Nat) : Array FloatArray :=
  let st := match mem.get? seat with
    | some (turn, st) => if turn == s.turnsTaken then st else net.atTurnStart st
    | none => net.atTurnStart net.initState
  net.atDecision st

/-- The policy bot's events for this seat, best first: the rule-based bot's reactions, then the network's move.
An error is a bug to report, not something to play around. -/
def candidatesWith (net : Net) (mem : Memory) (g : Game) (seat : Nat) (mayVote : Nat → Bool := fun _ => true) :
    Except String (List Json) := do
  let some s := g.state | return []
  let reactions := if s.openProposals.isEmpty && s.offers.isEmpty then [] else
    ((handEvents (Ctx.of g.spec.G) s [seat] mayVote).filterMap eventJson?).filter isReactionJson
  let move ← turnEventFrom net (mem.stateOf net s seat) g s seat
  return reactions ++ ((move.map (·.1)).toList.filterMap eventJson?)

/-- The policy bot's events for this seat. If the network did not load, or a decision fails, the error is
printed to the server's log as a bug and the seat does nothing; there is no fallback to another bot. -/
def candidates (mem : Memory) (g : Game) (seat : Nat) (mayVote : Nat → Bool := fun _ => true) : List Json :=
  match policyNet.bind fun net => candidatesWith net mem g seat mayVote with
  | .ok evs => evs
  | .error e => dbgTrace s!"policy bot bug: {e}" fun _ => []

/-- The memory after `ev` went through in game `g` (the game before it): if `ev` is the move the network chose for
the seat whose turn it was, that seat's state moves on. Votes and other reactions leave it alone, as in training,
where the network never voted. -/
def Memory.after (mem : Memory) (net : Net) (g : Game) (ev : Json) : Memory := Id.run do
  let some s := g.state | return mem
  let some seat := s.currentSeat | return mem
  if !g.isBot seat || isReactionJson ev then return mem
  match turnEventFrom net (mem.stateOf net s seat) g s seat with
  | .ok (some (mine, _, st)) =>
    if (eventJson? mine).map (·.compress) == some ev.compress then mem.insert seat (s.turnsTaken, st) else mem
  | _ => mem

/-- Every table's memory, by table code. It lives as long as the server process: after a restart, a seat's
state starts again from zero. -/
initialize memories : IO.Ref (Std.HashMap String Memory) ← IO.mkRef {}

/-- This table's memory. -/
def memoryOf (code : String) : IO Memory := do
  return (← memories.get).getD code {}

/-- Record that `ev` went through at table `code`, whose game before it was `g`. -/
def recordCommit (code : String) (g : Game) (ev : Json) : IO Unit := do
  if !policyOn then return
  let .ok net := policyNet | return
  let mem ← memoryOf code
  memories.modify (·.insert code (mem.after net g ev))

end CharterServer.Policy
