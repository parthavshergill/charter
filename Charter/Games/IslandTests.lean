import Charter.Engine
import Charter.Games.Island

/-!
# Tests of the Island's setup

**A settlement always has a place.** A settlement takes its spot and blocks at most three neighbours,
as the first test checks. A game has at most 8 setup settlements, so the 8th sees at most 28 blocked
spots of 54.

**A road has a place at 2 and 3 seats.** A one-time search of every first settlement, first road and
second settlement found no way to take all the links a seat could use. That search is not kept here, so
nothing in this project checks it again.

**At 4 seats a road can be blocked.** The game below shows it. Three other seats spend their roads on
every link around the first seat's pieces, and that seat then places a settlement with no free link.
The game does not stall: the seat ends its turn without that road.
-/

namespace Charter.Games.Island.Tests

open Charter Charter.Engine

abbrev G : GameDef := island

def fresh : State G := initialState G 4 1 [2]

-- No spot has more than 3 neighbours, so a settlement blocks at most 4 spots.
#guard (List.range G.map.spotCount).all fun v => (fresh.neighbours v).length ≤ 3
#guard 7 * 4 < G.map.spotCount

def placeAt (p : Seat) (k : PieceKind) (v : Nat) : Event := .move p (.place k (.spot v))
def placeOn (p : Seat) (k : PieceKind) (a b : Nat) : Event := .move p (.place k (.link (a, b)))
def endT (p : Seat) : Event := .move p .endTurn

/-- The game that blocks seat 0's second road. -/
def blockedRoadGame : List Event :=
  [ placeAt 0 "settlement" 25, placeOn 0 "road" 24 25, endT 0
  , placeAt 1 "settlement" 7, placeOn 1 "road" 24 7, endT 1
  , placeAt 2 "settlement" 11, placeOn 2 "road" 28 11, endT 2
  , placeAt 3 "settlement" 27, placeOn 3 "road" 26 27, endT 3
  , placeAt 3 "settlement" 42, placeOn 3 "road" 25 26, endT 3
  , placeAt 2 "settlement" 46, placeOn 2 "road" 28 29, endT 2
  , placeAt 1 "settlement" 50, placeOn 1 "road" 29 24, endT 1
  , placeAt 0 "settlement" 29 ]

def blocked : Option (State G) := (replay G 4 1 [2] blockedRoadGame).toOption

-- Seat 0 has no legal place for its road, and it can still end its turn.
#guard match blocked with
  | some s => (legalMoves G s 0).all (· == .endTurn) && (step G s (endT 0)).toOption.isSome
  | none => false

end Charter.Games.Island.Tests
