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

There is no fallback inside this path. A game that does not fit the network's layout is refused when the bot
joins (`problems`), and the reason is shown.

The recurrent state starts at zero for every decision: see `README` of this folder for why, and what it costs.
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
    if n.obsSize != baseSize || n.actSize != actSize then
      return .error s!"{path}: observation {n.obsSize} and actions {n.actSize}, expected {baseSize} and {actSize}"
    return .ok n

/-- The network, loaded once when the server starts, if the policy bot is on. -/
initialize policyNet : Except String Net ← do
  if !policyOn then return .error "the policy bot is off (CHARTER_BOT is not policy)"
  loadNet (← weightsPath)

/-- Does some law in force read a declared number? Then declaring can matter, and it is offered. -/
def declaresNow (s : State G) : Bool :=
  G.foundingLaws.any Policy.Law.readsDeclared || s.laws.any fun (_, L) => Policy.Law.readsDeclared L

/-- What the network sees of this game. -/
def tablesOf (g : Game) (s : State g.spec.G) : Tables :=
  Tables.make g.spec.G (g.spec.layout.spots.map (·.toPixel 1.0)) (declaresNow s)

/-- Why the network cannot play this game now, if it cannot. -/
def problems (g : Game) : List String :=
  match g.state with
  | some s => problemsOf g.spec.G s.rules.pieces s.laws.length
  | none => problemsOf g.spec.G g.spec.G.pieces g.spec.G.startingLaws.length

/-- The network's move for this seat on its turn, as an event, and how many actions were legal.
`none` when it is not this seat's turn. -/
def turnEvent (net : Net) (g : Game) (s : State g.spec.G) (seat : Nat) : Except String (Option (Event × Nat)) := do
  if s.currentSeat != some seat || s.phase == .ended then return none
  let G := g.spec.G
  let T := tablesOf g s
  let ep := (Episode.make G).seat s.rules.pieces
  let ctx := Ctx.of G
  let d : Decision := .turn seat
  let acts := legal T ep ctx s d
  if acts.isEmpty then
    throw s!"seat {seat} has its turn and no legal action has a number in the layout"
  let obs := observe T ep ctx (template T ep G s.turnOrder.length) s d
  let (logits, _) ← net.forward obs net.initState
  let some a := net.best logits (acts.map (·.1)).toArray
    | throw "no legal action was scored"
  match acts.find? (·.1 == a) with
  | some (_, ev) => return some (ev, acts.length)
  | none => throw s!"action {a} has no event"

/-- Is this event a reaction (a vote, a signature or an accepted offer), not a move on the seat's turn? -/
def isReactionJson (ev : Json) : Bool :=
  match jStr ev "t" with
  | some "vote" | some "sign" => true
  | some "move" => (jField ev "move").bind (jStr · "t") == some "accept"
  | _ => false

/-- The policy bot's events for this seat, best first: the rule-based bot's reactions, then the network's move.
An error is a bug to report, not something to play around. -/
def candidatesWith (net : Net) (g : Game) (seat : Nat) (mayVote : Nat → Bool := fun _ => true) :
    Except String (List Json) := do
  let some s := g.state | return []
  let reactions := if s.openProposals.isEmpty && s.offers.isEmpty then [] else
    ((handEvents (Ctx.of g.spec.G) s [seat] mayVote).filterMap eventJson?).filter isReactionJson
  let move ← turnEvent net g s seat
  return reactions ++ ((move.map (·.1)).toList.filterMap eventJson?)

/-- The policy bot's events for this seat. If the network did not load, or a decision fails, the error is
printed to the server's log as a bug and the seat does nothing; there is no fallback to another bot. -/
def candidates (g : Game) (seat : Nat) (mayVote : Nat → Bool := fun _ => true) : List Json :=
  match policyNet.bind fun net => candidatesWith net g seat mayVote with
  | .ok evs => evs
  | .error e => dbgTrace s!"policy bot bug: {e}" fun _ => []

end CharterServer.Policy
