import Server.Seat
import Server.Suggest

/-!
# Testing the choke point on a real game

`nobody_sees_what_is_hidden` is about `observe`. This file tests that what the server sends is built
from it. It plays two tables of High Card with the same moves and different server seeds, chosen so that
seat 0 draws the same cards at both, and seat 1 does not. After every event it compares what seat 0, and a
spectator, would be sent: the whole view, the scene, a Claude seat's prompt, the clerk's prompt, and what
a bot would do. They must be the same at both tables. Seat 1's view must differ, or the test would prove
nothing.

The seeds are 1 and 216. Seat 0 draws 7 and then 8 at both. Seat 1 draws 4 at one and 5 at the other, so
seat 0's 7 wins the first round at both, and the showdown pays the same.
-/

namespace CharterServer.SecrecyCheck

open Lean Charter CharterServer CharterServer.Game

/-- A two-seat table of this game with this server seed, started. -/
def tableOf (game : String) (seed : Nat) : Game :=
  let made := create (Json.mkObj [("t", "create"), ("code", "HC"), ("seats", toJson (2 : Nat)),
    ("game", game), ("_serverSeed", toJson seed)])
  match made with
  | .error _ => default
  | .ok g =>
    let joined := (List.range 2).foldl (fun (g : Game) i =>
      match apply g (Json.mkObj [("t", "join"), ("name", s!"P{i}"), ("kind", "human"), ("_token", s!"t{i}"), ("nonce", toJson i)]) with
      | .ok g' => g'
      | .error _ => g) g
    match apply joined (Json.mkObj [("t", "start")]) with
    | .ok g' => g'
    | .error _ => default

/-- A two-seat High Card table with this server seed, started. -/
def table (seed : Nat) : Game := tableOf "high-card" seed

-- The seeds give the cards the file's header says.
#guard
  let G := Games.HighCard.game
  let rolls (n : Nat) := (List.range 3).map (rollAt G (combineSeed (UInt64.ofNat n) [0, 1]))
  rolls 1 == [7, 4, 8] && rolls 216 == [7, 5, 8]

/-- The next event to play: in setup, place a piece and end the turn; in play, bet one more chip than
the seat's number, then end the turn. -/
def nextEvent (g : Game) : Option Json :=
  match g.state with
  | none => none
  | some s =>
    match s.currentSeat with
    | none => none
    | some p =>
      if s.phase == .ended then none
      else if s.phase == .setup then
        let legal := Engine.legalMoves g.spec.G s p
        match legal.find? (fun | .place .. => true | _ => false) with
        | some m => some (Bots.moveEvent p m)
        | none => some (Bots.moveEvent p .endTurn)
      else if s.actionsThisTurn p == 0 then some (Bots.moveEvent p (.declare "chips" (p + 1)))
      else some (Bots.moveEvent p .endTurn)

/-- Play both tables with the same events until round 2 is under way. -/
def play (n : Nat) : List (Game × Game) :=
  let rec go : Nat → Game → Game → List (Game × Game)
    | 0, _, _ => []
    | k + 1, a, b =>
      match nextEvent a with
      | none => []
      | some ev =>
        match apply a ev, apply b ev with
        | .ok a', .ok b' =>
          if (a'.state.map (·.round)).getD 0 > 2 then [] else (a', b') :: go k a' b'
        | _, _ => []
  go n (table 1) (table 216)

def steps : List (Game × Game) := play 40

/-- The view without the fingerprint, which names the server seed's hash, and is meant to differ. -/
def viewText (g : Game) (v : Option Nat) : String :=
  match View.view g "HC" v [] {} with
  | .obj kvs => (Json.obj (kvs.erase "fingerprint")).compress
  | j => j.compress

/-- Everything this viewer is sent, or would be sent, as text. -/
def sentTo (g : Game) (v : Option Nat) : List String :=
  let seen := g.seenBy v
  let scene := match seen with
    | some s => toString (Scene.sceneBytes g.spec.layout s v).toList
    | none => ""
  let prompts := match v, g.state with
    | some p, some s0 =>
      let sit := Player.situation g s0 p
      let clerk := match seen with
        | some s => Formalize.tableContext g s p ++ Suggest.publicFacts g s
        | none => ""
      [Seat.gameBlock sit {}, Seat.legalBlock sit, clerk, (Json.arr (Bots.candidatesFor g [p]).toArray).compress]
    | _, _ => []
  [viewText g v, scene] ++ prompts

-- The test ran far enough to mean something: it reached the second round.
#guard steps.length > 10 && steps.getLast?.any fun (a, _) => (a.state.map (·.round)) == some 2

-- **Seat 0 and a spectator are sent the same at both tables, after every event.**
#guard steps.all fun (a, b) => sentTo a (some 0) == sentTo b (some 0) && sentTo a none == sentTo b none

-- Seat 1 sees its own card, so its view differs. Without this the test above could pass by hiding
-- everything.
#guard steps.any fun (a, b) => viewText a (some 1) != viewText b (some 1)

-- The engine itself holds different cards at the two tables.
#guard steps.any fun (a, b) =>
  (a.state.map (·.balance (.player 1) "card")) != (b.state.map (·.balance (.player 1) "card"))

/-! ## The server refuses trades of hidden goods -/

#guard (overLimit (table 1) (Bots.moveEvent 0 (.bankTrade "chips" "card"))).isSome
#guard (overLimit (table 1) (Bots.moveEvent 0 (.offer none [("card", 1)] [("chips", 1)]))).isSome
#guard (overLimit (table 1) (Bots.moveEvent 0 (.offer none [("chips", 1)] [("chips", 2)]))).isNone

/-! ## While the game runs, `/events` shows no sealed number -/

#guard
  let g := (steps.getLast?.map (·.1)).getD default
  let ev := Bots.moveEvent 0 (.declare "chips" 3)
  !((View.eventSeen g ev).compress.splitOn "3").length > 1

/-! ## A game that hides nothing is not changed

Its chronicle has no copies, and each seat's view has every hand. -/

#guard (tableOf "island" 1).state.isSome && (tableOf "island" 1).seen.isEmpty
#guard
  let g := tableOf "island" 1
  (g.seenBy (some 0)).map (·.books .bank "grain") == g.state.map (·.books .bank "grain")

end CharterServer.SecrecyCheck
