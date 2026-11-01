/-!
# Names, limits and what a game is

A game is data. These are its parts. `Words/GameDef.lean` puts them together, and `GameDef.Valid`
in `Words/Valid.lean` checks a whole game.
-/

namespace Charter

/-! ## Names -/

/-- A player's seat. The engine never uses the number's size, only its identity. -/
abbrev Seat := Nat
/-- A resource, such as `"grain"` or `"helium"`. -/
abbrev Res := String
/-- A piece type, such as `"road"` or `"outpost"`. -/
abbrev PieceKind := String
/-- A list of resources and amounts, such as a price. -/
abbrev Bundle := List (Res × Nat)

/-! ## Limits -/

/-- The fewest seats in a game. -/
def minSeats : Nat := 2
/-- The most seats in a game. -/
def maxSeats : Nat := 6
/-- The most rounds a game can set. -/
def maxRoundsAllowed : Nat := 60
/-- The most spots a map can have. -/
def maxSpots : Nat := 100
/-- The most resources a game can have. -/
def maxResources : Nat := 16
/-- The most kinds of piece a game can have, counting those laws add. -/
def maxPieceKinds : Nat := 16
/-- The most of one resource a game can have. -/
def maxStock : Nat := 2000
/-- The most laws that can be in force at once. -/
def maxLawsInForce : Nat := 48
/-- The largest size a law can have. `Law.size` measures it. -/
def maxLawSize : Nat := 128
/-- The most entries one law can ask for on one trigger, when every condition is true. This keeps a
turn fast: a `forEach` inside a `forEach` multiplies the entries by the number of seats each time.
At 6 seats this allows a `forEach` with 21 transfers, or one `forEach` inside another with 3. -/
def maxPlannedEntries : Nat := 128
/-- The most entries all the laws in force can ask for together on one trigger. A harvest runs every
law once per payment, so this keeps a harvest fast. 42 laws of one `forEach` with one transfer use 252
at 6 seats. -/
def maxPlannedTotal : Nat := 256
/-- The most numbers and tests all the laws in force can read together on one trigger. A harvest runs
every law once per payment, so most of a harvest's time goes here. `Law.reads` counts them. -/
def maxReadsTotal : Nat := 8192
/-- How many events one seat can send per turn. Every event except ending a turn counts: places,
trades, offers, accepts, cancels, proposals, votes, signatures and exits. -/
def maxActionsPerTurn : Nat := 20
/-- The most open proposals one seat can have. -/
def maxOpenPerSeat : Nat := 2
/-- The most deals that can run at once. -/
def maxActiveDeals : Nat := 8
/-- Deals get an id only when they start. Ids are below this number. -/
def maxDealsPerGame : Nat := 64

/-! ## A game definition -/

/-- A resource and how much of it the game has. -/
structure ResourceDef where
  name : Res
  stock : Nat
  deriving Repr, DecidableEq

/-- Where a piece can go. This list is fixed, so a game cannot invent a new kind of move. -/
inductive Placement where
  /-- On a free link that touches one of the owner's pieces. -/
  | link
  /-- On a free spot, with no piece on a neighbouring spot, connected to the owner's links. -/
  | spot
  /-- On top of the owner's piece of the given kind, which it replaces. -/
  | upgrade (of : PieceKind)
  /-- On the owner's piece of the given kind, which stays. -/
  | attach (to : PieceKind)
  deriving Repr, DecidableEq

/-- A kind of piece: its price, points, where it can go, and what it collects. -/
structure PieceDef where
  name : PieceKind
  cost : Bundle
  points : Nat
  placement : Placement
  /-- How many resources this piece collects when a neighbouring region produces. -/
  yield : Nat
  /-- The most of this piece one seat can own. -/
  limit : Nat
  deriving Repr, DecidableEq

/-- A region produces its resource when the dice show its number. -/
structure Region where
  res : Res
  number : Nat
  spots : List Nat
  deriving Repr, DecidableEq

/-- The map: numbered spots, the links between them, and the regions that produce. -/
structure MapGraph where
  spotCount : Nat
  links : List (Nat × Nat)
  regions : List Region
  deriving Repr, DecidableEq

end Charter
