import Server.Game
import Server.Bots
import Server.Policy.Bot

/-!
# The player interface

A person, a rule-based bot and a Claude seat are the same thing to the server. Each is shown a seat's
`Situation`, and each answers with a `Choice`: the events it wants, in the order to try them. The
engine has the final word on every one of them.

A person's answer comes later, through the web page, so a person's `choose` says `wait`. The driver in
`Server/Driver.lean` asks the other two.
-/

namespace CharterServer.Player
open Lean Charter CharterServer.Game

/-- What one seat can see and do right now. -/
structure Situation where
  game : Game
  seat : Nat
  /-- The current state of the game. -/
  state : State game.spec.G
  /-- The moves `Engine.step` accepts from this seat now, except offers. Worked out when asked for. -/
  legal : Thunk (List Move)
  /-- Open laws this seat has not voted on. -/
  votes : List OpenProposal
  /-- Open deals this seat should sign and has not. -/
  signs : List OpenProposal
  /-- Open offers this seat could accept now. Worked out when asked for. -/
  offers : Thunk (List Offer)
  /-- It is this seat's turn. -/
  myTurn : Bool

/-- Build the situation of a seat. -/
def situation (g : Game) (s : State g.spec.G) (seat : Nat) : Situation :=
  let G := g.spec.G
  { game := g, seat, state := s
    legal := Thunk.mk fun _ => Engine.legalMoves G s seat
    votes := s.openProposals.filter fun p =>
      (match p.body with
       | .law _ => true
       | .deal _ => false) && !(p.votes.any (·.1 == seat))
    signs := s.openProposals.filter fun p =>
      match p.body with
      | .deal d => d.signers.contains seat && !p.signed.contains seat
      | .law _ => false
    offers := Thunk.mk fun _ => s.offers.filter fun o => (Engine.step G s (.move seat (.accept o.id))).toOption.isSome
    myTurn := s.currentSeat == some seat && s.phase != .ended }

/-- What a player answers. -/
inductive Choice where
  /-- Try these events, in this order. -/
  | act (events : List Json)
  /-- Nothing yet. -/
  | wait

/-- One player. -/
structure Player where
  kind : String
  /-- Its choice, as a pure function, for a player that needs no outside service. The driver can run
  this inside its lock, and it merges the answers of all such seats by `merged`. -/
  policy : Option (Situation → List Json) := none
  choose : Situation → IO Choice
  /-- Told what the engine said to an event this player chose: `none` means accepted. -/
  told : Json → Option String → IO Unit := fun _ _ => pure ()
  /-- Called after its events have gone to the engine. -/
  after : IO Unit := pure ()

/-- A person answers through the web page. -/
def human : Player := { kind := "human", choose := fun _ => pure .wait }

/-- The bot: the rule-based bot of `Server/Bots.lean`, or the trained policy of `Server/Policy/Bot.lean` when the
server runs with `CHARTER_BOT=policy`. -/
def botPolicy (sit : Situation) : List Json :=
  if Policy.policyOn then Policy.candidates sit.game sit.seat
  else Bots.candidatesFor sit.game [sit.seat]

def bot : Player :=
  { kind := "bot"
    policy := some botPolicy
    choose := fun sit => pure (.act (botPolicy sit)) }

/-! ## The order of events from several rule-based seats

Reactions come before moves: votes and signatures by proposal, then accepted offers by offer, then the
current seat's move. Seats are in order within each. -/

/-- Where an event goes in that order. -/
def orderKey (ev : Json) : Nat × Nat :=
  match jStr ev "t" with
  | some "vote" | some "sign" => (0, (jNat ev "id").getD 0)
  | some "move" =>
    match (jField ev "move").bind (jStr · "t") with
    | some "accept" => (1, ((jField ev "move").bind (jNat · "id")).getD 0)
    | _ => (2, 0)
  | _ => (2, 0)

/-- Is this a reaction, which a seat can make out of turn, not a move on its turn? -/
def isReaction (ev : Json) : Bool := (orderKey ev).1 < 2

/-- Join several seats' candidates in that order. The sort is stable, so seats stay in order. -/
def merged (lists : List (List Json)) : List Json :=
  let keyed := lists.flatten.zipIdx
  ((keyed.toArray.qsort fun a b =>
      let ka := orderKey a.1
      let kb := orderKey b.1
      ka.1 < kb.1 || (ka.1 == kb.1 && (ka.2 < kb.2 || (ka.2 == kb.2 && a.2 < b.2)))).toList).map (·.1)

/-- What the rule-based seats do next, if anything: the first event the engine accepts. -/
def nextRuleEvent (g : Game) : Option Json :=
  match g.state with
  | none => none
  | some s =>
    let lists := g.botSeats.map fun seat => botPolicy (situation g s seat)
    (merged lists).find? fun ev => (apply g ev).toOption.isSome

end CharterServer.Player
