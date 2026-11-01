import Charter.Engine
import Charter.Games.PirateRepublic

/-!
# The Pirate Republic, played

Each founding law played through `Engine.step`. Tables are built by hand, with the pieces and hands each
test needs. Whole games are in `scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.PirateRepublic.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh : St := initialState game 4 1 [2]

/-- Hand a seat some goods from the bank. -/
def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

/-- The chest as it stands after the first roll: it holds the hats, the ballots and the pardons. -/
def stocked (s : St) : St :=
  { s with books := (s.books.postAll
      [⟨.bank, .treasury, "hat", 2, .trade⟩, ⟨.bank, .treasury, "ballot", 12, .trade⟩, ⟨.bank, .treasury, "pardon", 4, .trade⟩]).getD s.books }

def table (pieces : List Piece := []) : St :=
  stocked { fresh with phase := .actions, pieces := pieces }

/-- From the chest to a seat, as an earlier law would have paid it. -/
def award (s : St) (p : Seat) (r : Res) (n : Nat) : St :=
  { s with books := (s.books.postAll [⟨.treasury, .player p, r, n, .trade⟩]).getD s.books }

def declaring (s : St) (ds : List (Seat × Res × Nat)) : St :=
  { s with declared := fun p r => ((ds.find? fun d => d.1 == p && d.2.1 == r).map (·.2.2)).getD 0 }

def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r

/-- Every seat ends its turn, so the round ends and the next one's first roll happens. -/
def endRound (s : St) : Option St :=
  (List.range 4).foldlM (fun x _ => (step game x .forceEndTurn).toOption) s

/-- Each seat holds a ballot, seat 2 holds a second one. -/
def ballots : St :=
  award (award (award (award (award (table) 0 "ballot" 1) 1 "ballot" 1) 2 "ballot" 2) 3 "ballot" 1) 0 "hat" 1

/-! ## The chest -/

-- The first roll moves the spare hats, ballots and pardons to the chest, so the bank has none to sell.
#guard match (step game { fresh with phase := .actions } .forceEndTurn).toOption with
  | some s =>
    [s.balance .bank "hat", s.balance .bank "ballot", s.balance .bank "pardon"] == [0, 0, 0] &&
      [s.balance .treasury "hat", s.balance .treasury "ballot", s.balance .treasury "pardon"] == [2, 12, 4]
  | none => false

-- The first round's end hands out the first ballots.
#guard match endRound { fresh with phase := .actions } with
  | some s => [0, 1, 2, 3].all fun p => holds s p "ballot" == 1 && holds s p "hat" == 0
  | none => false

/-! ## The vote -/

-- Seat 2 alone declares the most, and the captain is deposed. Ballots go back, and each seat gets 1.
#guard match endRound (declaring ballots [(2, "ballot", 2), (0, "ballot", 1)]) with
  | some s => holds s 2 "hat" == 1 && holds s 0 "hat" == 0 && [0, 1, 2, 3].all (holds s · "ballot" == 1)
  | none => false

-- A tie leaves the hat where it is.
#guard match endRound (declaring ballots [(1, "ballot", 1), (3, "ballot", 1)]) with
  | some s => holds s 0 "hat" == 1 && holds s 1 "hat" == 0 && holds s 3 "hat" == 0
  | none => false

-- With no declarations the hat stays.
#guard match endRound ballots with
  | some s => holds s 0 "hat" == 1
  | none => false

-- A declaration counts only as far as the ballots a seat holds: seat 3 declares 9 and holds 1.
#guard match endRound (declaring ballots [(3, "ballot", 9), (2, "ballot", 2)]) with
  | some s => holds s 2 "hat" == 1 && holds s 3 "hat" == 0
  | none => false

-- The sitting captain can win again and keeps exactly one hat.
#guard match endRound (declaring (award ballots 0 "ballot" 2) [(0, "ballot", 3), (2, "ballot", 2)]) with
  | some s => holds s 0 "hat" == 1 && s.balance .treasury "hat" == 1
  | none => false

/-! ## The double share -/

/-- A wharf on the first plunder tile for seat 1. -/
def plunderCorner : Nat := ((game.map.regions.find? (·.res == "plunder")).map (·.spots.getD 0 0)).getD 0
def plunderNumber : Nat := ((game.map.regions.find? (·.res == "plunder")).map (·.number)).getD 0

/-- The next roll is this number. -/
def rolling (s : St) (r : Nat) : St :=
  { s with rollsMade := ((List.range 500).find? (fun k => rollAt game s.seed k == r)).getD 0 }

-- Seat 1 is paid 1 plunder. The hat gets the same, and each is worth a point.
#guard match (step game (rolling (award (table [⟨1, "wharf", .spot plunderCorner⟩]) 0 "hat" 1) plunderNumber) .forceEndTurn).toOption with
  | some s => holds s 1 "plunder" == 1 && holds s 0 "plunder" == 1 && s.pointsOf 0 == 1 && s.pointsOf 1 == 2
  | none => false

-- Other goods are not copied. A timber tile pays only the seat on it.
def timberCorner : Nat := ((game.map.regions.find? (·.res == "timber")).map (·.spots.getD 0 0)).getD 0
def timberNumber : Nat := ((game.map.regions.find? (·.res == "timber")).map (·.number)).getD 0
#guard match (step game (rolling (award (table [⟨1, "wharf", .spot timberCorner⟩]) 0 "hat" 1) timberNumber) .forceEndTurn).toOption with
  | some s => holds s 1 "timber" == 1 && holds s 0 "timber" == 0
  | none => false

/-! ## The levy -/

def levyTable : St :=
  give (give (give (award (table) 0 "hat" 1) 1 [("rum", 2)]) 2 [("rum", 4)]) 0 [("rum", 1)]

-- The captain declares 9, which counts as 3. Seat 1 pays the 2 it has, seat 2 pays 3, and seat 3 has none.
#guard match endRound (declaring levyTable [(0, "rum", 9)]) with
  | some s => [holds s 0 "rum", holds s 1 "rum", holds s 2 "rum", holds s 3 "rum"] == [6, 0, 1, 0]
  | none => false

-- A levy of nothing costs nothing.
#guard match endRound levyTable with
  | some s => [holds s 0 "rum", holds s 1 "rum", holds s 2 "rum"] == [1, 2, 4]
  | none => false

-- Only the hat can call a levy. Another seat's declared rum does nothing.
#guard match endRound (declaring levyTable [(1, "rum", 3)]) with
  | some s => [holds s 0 "rum", holds s 1 "rum", holds s 2 "rum"] == [1, 2, 4]
  | none => false

/-! ## The Navy -/

def corners : List Nat := (List.range game.map.spotCount).filter (· % 7 == 0)
def spotOf (i : Nat) : Nat := corners.getD i 0

/-- Each seat has two wharves, and seat 3 has a fort as well. -/
def fleet : List Piece :=
  [0, 1, 2, 3].flatMap fun p =>
    [⟨p, "wharf", .spot (spotOf (2 * p))⟩, ⟨p, "wharf", .spot (spotOf (2 * p + 1))⟩]

def navy (round : Nat) : St :=
  declaring
    { give (give (table fleet) 0 [("plunder", 5)]) 1 [("powder", 4)] with round := round }
    [(0, "pardon", 1), (1, "powder", 3), (2, "powder", 3)]

def wharves (s : St) (p : Seat) : Nat := s.countOf p "wharf"

-- Round 5: seat 0 takes the pardon and pays half its plunder, rounded down. Seat 1 pays 3 powder and fights.
-- Seat 2 declared powder but holds none, so it burns, as does seat 3, which declared nothing.
#guard match endRound (navy 5) with
  | some s =>
    holds s 0 "pardon" == 1 && holds s 0 "plunder" == 3 && wharves s 0 == 2 &&
      holds s 1 "powder" == 1 && wharves s 1 == 2 &&
      wharves s 2 == 1 && wharves s 3 == 1
  | none => false

-- In any other round the Navy does nothing.
#guard match endRound (navy 4) with
  | some s =>
    holds s 0 "pardon" == 0 && holds s 0 "plunder" == 5 && holds s 1 "powder" == 4 &&
      [0, 1, 2, 3].all (wharves s · == 2)
  | none => false

-- A pardon is worth 3 points, and from then on plunder from the dice goes back.
def pardoned : St := award (table [⟨1, "wharf", .spot plunderCorner⟩]) 1 "pardon" 1
#guard pardoned.pointsOf 1 == 4
#guard match (step game (rolling pardoned plunderNumber) .forceEndTurn).toOption with
  | some s => holds s 1 "plunder" == 0
  | none => false

-- A captain who took the pardon still gets the hat's copy of what others bring in. The law says so.
#guard match (step game (rolling (award (award (table [⟨1, "wharf", .spot plunderCorner⟩]) 0 "pardon" 1) 0 "hat" 1) plunderNumber) .forceEndTurn).toOption with
  | some s => holds s 0 "plunder" == 1
  | none => false

-- The hat itself can be handed over by an offer: it is an ordinary good.
#guard game.pieces.any fun d => d.cost.any (·.1 == "hat")

end Charter.Games.PirateRepublic.Tests
