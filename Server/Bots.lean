import Server.Game
import Server.BotCore

/-!
# Bot seats

A bot is an ordinary seat that the server plays. `candidatesFor` lists events for the bots, best first.
The driver commits the first one that `Game.apply` accepts, so every bot action goes through
`Engine.step`. The policy is in `Server/BotCore.lean`. This file joins it to a table.
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

/-- The setup move out of these legal moves: the best spot, then the road toward the best site. -/
def setupMove (s : State G) (legal : List Move) : Move :=
  setupFrom (Ctx.of G) s legal fun _ => true

/-- Candidate events for these seats, best first. `mayVote` says which laws can be voted on now. -/
def candidatesFor (g : Game) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) : List Json :=
  match g.state with
  | none => []
  | some s =>
    -- The board takes some work to make, so do not make it for a seat with nothing to do.
    if s.openProposals.isEmpty && s.offers.isEmpty && !(s.currentSeat.any bots.contains) then [] else
    -- In a game that hides something, each bot decides from what it may know.
    if g.marked then
      bots.flatMap fun b => (handEvents (Ctx.of g.spec.G) (observe g.secrecy (some b) s) [b] mayVote).filterMap eventJson?
    else (handEvents (Ctx.of g.spec.G) s bots mayVote).filterMap eventJson?

/-- The first of these seats' candidates that the engine accepts. -/
def nextFor? (g : Game) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) : Option Json :=
  (candidatesFor g bots mayVote).find? fun ev => (apply g ev).toOption.isSome

/-- What the bots at this table do next. -/
def next? (g : Game) : Option Json := nextFor? g g.botSeats

end CharterServer.Bots
