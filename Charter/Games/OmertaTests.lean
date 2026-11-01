import Charter.Engine
import Charter.Games.Omerta

/-!
# Omertà, played

Each founding law played through `Engine.step`. Tables are built by hand, with the pieces and hands each
test needs. Whole games are in `scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.Omerta.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh : St := initialState game 4 1 [2]

/-- Hand a seat some goods from the bank. -/
def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

/-- Put cash in the reward, as earlier rolls would have. -/
def fund (s : St) (n : Nat) : St :=
  { s with books := (s.books.postAll [⟨.bank, .treasury, "cash", n, .trade⟩]).getD s.books }

def declaring (s : St) (ds : List (Seat × Res × Nat)) : St :=
  { s with declared := fun p r => ((ds.find? fun d => d.1 == p && d.2.1 == r).map (·.2.2)).getD 0 }

def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r
def rackets (s : St) (p : Seat) : Nat := s.countOf p "racket"

def corners : List Nat := (List.range game.map.spotCount).filter (· % 7 == 0)
def spotOf (i : Nat) : Nat := corners.getD i 0

/-- Each seat has two fronts, each with a racket in the back. Seat 3 has a third front with no racket. -/
def family : List Piece :=
  ([0, 1, 2, 3].flatMap fun p =>
    [⟨p, "front", .spot (spotOf (2 * p))⟩, ⟨p, "front", .spot (spotOf (2 * p + 1))⟩,
     ⟨p, "racket", .spot (spotOf (2 * p))⟩, ⟨p, "racket", .spot (spotOf (2 * p + 1))⟩]) ++
    [⟨3, "front", .spot (spotOf 9)⟩]

/-- The table in the middle of a round, at seat `i`'s turn. Everyone holds 1 dirt. The reward is 20. -/
def table (i : Nat) : St :=
  fund (give (give (give (give { fresh with phase := .actions, pieces := family, turnIndex := i }
    0 [("dirt", 1)]) 1 [("dirt", 1)]) 2 [("dirt", 1)]) 3 [("dirt", 1)]) 20

/-- The current seat ends its turn. -/
def next (s : St) : Option St := (step game s .forceEndTurn).toOption

/-- The cash in the reward. -/
def reward (s : St) : Nat := s.balance .treasury "cash"

/-! ## Talking -/

-- Seat 0 talks on its turn. At the roll that starts seat 1's turn it takes all 20 of the reward, and it
-- hands over its dirt. Both its rackets close. Every other seat loses one racket, and keeps its dirt.
-- The roll then puts 1 back in the reward.
#guard match next (declaring (table 0) [(0, "dirt", 1)]) with
  | some s =>
    holds s 0 "cash" == 20 && holds s 0 "dirt" == 0 && rackets s 0 == 0 &&
      [1, 2, 3].all (fun p => rackets s p == 1 && holds s p "dirt" == 1) && reward s == 1
  | none => false

-- Talking costs the talker its rackets, but not its fronts.
#guard match next (declaring (table 0) [(0, "dirt", 1)]) with
  | some s => s.countOf 0 "front" == 2
  | none => false

-- The reward goes once. Seat 1 plays on after seat 0 talked, and at the next roll nobody is paid again,
-- though seat 0's declaration still stands.
#guard match (next (declaring (table 0) [(0, "dirt", 1)])).bind next with
  | some s => holds s 0 "cash" == 20 && rackets s 1 == 1 && reward s == 2
  | none => false

-- Declaring dirt with no dirt in hand is not talking: nothing happens but the roll's 1.
#guard match next (declaring { table 0 with books := ((table 0).books.postAll [⟨.player 0, .bank, "dirt", 1, .trade⟩]).getD (table 0).books } [(0, "dirt", 3)]) with
  | some s => holds s 0 "cash" == 0 && rackets s 0 == 2 && reward s == 21
  | none => false

-- Seat 3 is last in the round. If it talks, it is paid at the round's end, before the declarations clear,
-- and nobody's rackets pay that round.
#guard match next (declaring (table 3) [(3, "dirt", 1)]) with
  | some s =>
    holds s 3 "cash" == 20 && rackets s 3 == 0 && [0, 1, 2].all (fun p => rackets s p == 1 && holds s p "cash" == 0)
  | none => false

/-! ## The take -/

-- Nobody talks. At the round's end each racket pays its owner 1 cash, and cash is worth a point:
-- two fronts, two rackets and two cash make 6.
#guard match next (table 3) with
  | some s => [0, 1, 2, 3].all (fun p => holds s p "cash" == 2 && rackets s p == 2) && s.pointsOf 0 == 6
  | none => false

/-! ## The heat -/

-- A new racket puts 2 cash in the reward and gives its builder 1 dirt.
def building : St :=
  give { fresh with phase := .actions, pieces := [⟨0, "front", .spot (spotOf 0)⟩] } 0 [("wine", 2), ("fish", 1)]

#guard match step game building (.move 0 (.place "racket" (.spot (spotOf 0)))) with
  | .ok s => reward s == 2 && holds s 0 "dirt" == 1 && rackets s 0 == 1
  | .error _ => false

-- Every roll puts 1 cash in the reward.
#guard match next { fresh with phase := .actions } with
  | some s => reward s == 1
  | none => false

end Charter.Games.Omerta.Tests
