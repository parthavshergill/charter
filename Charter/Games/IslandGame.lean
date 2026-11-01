import Charter.Games.Island
import Charter.Engine

/-!
# The parts of a full game of the Island

`scripts/island_game.lean` plays a game with these parts and writes its events to
`Charter/Games/IslandGameEvents.lean`. `Charter/Proofs/IslandWitness.lean` has the kernel replay them.
-/

namespace Charter.Games.Island

open Charter

/-- A seat ends its turn. -/
def endTurn (p : Seat) : Event := .move p .endTurn
/-- A seat places a piece on a spot. -/
def buildAt (p : Seat) (k : PieceKind) (v : Nat) : Event := .move p (.place k (.spot v))
/-- A seat places a piece on a link. -/
def buildOn (p : Seat) (k : PieceKind) (a b : Nat) : Event := .move p (.place k (.link (a, b)))
/-- A seat trades with the bank. -/
def trade (p : Seat) (give get : Res) : Event := .move p (.bankTrade give get)

/-- The law in this game: at each round's end, the bank pays every seat 1 grain. -/
def commonGrain : Law :=
  { title := "Common grain"
    clauses := [.onRoundEnd [.forEach .yes [.transfer .bank .each (.lit "grain") (.lit 1)]]] }

/-- The deal in this game: for two rounds, seat `p` pays seat `q` 1 of a resource at each round's end. -/
def twoRoundGift (p q : Seat) (r : Res) : Deal :=
  { title := "A gift for two rounds", signers := [p, q], rounds := 2, exitNotice := 0
    deposits := [(p, r, 2)]
    terms := [.everyRound [{ src := p, dst := .seat q, res := r, amount := 1 }]] }

/-- The votes on this proposal, in the order they were cast. -/
def votesOn (id : Nat) (events : List Event) : List (Seat × Bool) :=
  events.filterMap fun
    | .vote seat n yes => if n == id then some (seat, yes) else none
    | _ => none

end Charter.Games.Island
