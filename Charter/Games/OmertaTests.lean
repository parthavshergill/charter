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

/-- The dirt the bank has not handed out, in the treasury, where the first roll puts it. -/
def stocked (s : St) : St :=
  { s with books := (s.books.postAll [⟨.bank, .treasury, "dirt", s.balance .bank "dirt", .trade⟩]).getD s.books }

/-- The table in the middle of a round, at seat `i`'s turn. Everyone holds 1 dirt. The reward is 20. -/
def table (i : Nat) : St :=
  stocked <| fund (give (give (give (give { fresh with phase := .actions, pieces := family, turnIndex := i }
    0 [("dirt", 1)]) 1 [("dirt", 1)]) 2 [("dirt", 1)]) 3 [("dirt", 1)]) 20

/-- The current seat ends its turn. -/
def next (s : St) : Option St := (step game s .forceEndTurn).toOption

/-- The cash in the reward. -/
def reward (s : St) : Nat := s.balance .treasury "cash"

/-! ## Talking -/

-- Seat 0 talks on its turn. At the roll that starts seat 1's turn it takes all 20 of the reward, and it
-- hands over its dirt. Both its rackets close. Every other seat loses one racket, and keeps its dirt.
-- The roll then puts 2 back in the reward, for the 8 rackets that ran when the dice fell.
#guard match next (declaring (table 0) [(0, "dirt", 1)]) with
  | some s =>
    holds s 0 "cash" == 20 && holds s 0 "dirt" == 0 && rackets s 0 == 0 &&
      [1, 2, 3].all (fun p => rackets s p == 1 && holds s p "dirt" == 1) && reward s == 2
  | none => false

-- Talking costs the talker its rackets, but not its fronts.
#guard match next (declaring (table 0) [(0, "dirt", 1)]) with
  | some s => s.countOf 0 "front" == 2
  | none => false

-- The reward goes once. Seat 1 plays on after seat 0 talked, and at the next roll nobody is paid again,
-- though seat 0's declaration still stands. Three rackets run now, too few to make the reward grow.
#guard match (next (declaring (table 0) [(0, "dirt", 1)])).bind next with
  | some s => holds s 0 "cash" == 20 && rackets s 1 == 1 && reward s == 2
  | none => false

-- Declaring dirt with no dirt in hand is not talking: nothing happens but the roll's 2.
#guard match next (declaring { table 0 with books := ((table 0).books.postAll [⟨.player 0, .bank, "dirt", 1, .trade⟩]).getD (table 0).books } [(0, "dirt", 3)]) with
  | some s => holds s 0 "cash" == 0 && rackets s 0 == 2 && reward s == 22
  | none => false

-- Seat 3 is last in the round, and sees what everyone did. If it talks, it is paid at the round's end,
-- before the declarations clear, and it gets only half the reward: 10 of 20. The other half stays, and the
-- 3 rackets left are too few to make the next round's first roll add to it. The others are paid for the rackets they ran
-- this round. They already hold dirt, so they get no more. The talker gets nothing.
#guard match next (declaring (table 3) [(3, "dirt", 1)]) with
  | some s =>
    holds s 3 "cash" == 10 && rackets s 3 == 0 && holds s 3 "dirt" == 0 && reward s == 10 &&
      [0, 1, 2].all (fun p => rackets s p == 1 && holds s p "cash" == 4 && holds s p "dirt" == 1)
  | none => false

/-! ## The take -/

-- Nobody talks. At the round's end each racket pays its owner 2 cash, and cash is worth a point:
-- two fronts, two rackets and four cash make 8. Everyone already holds dirt, and nobody holds more than 1.
#guard match next (table 3) with
  | some s => [0, 1, 2, 3].all (fun p => holds s p "cash" == 4 && rackets s p == 2 && holds s p "dirt" == 1) && s.pointsOf 0 == 8
  | none => false

-- A seat that runs a racket and holds no dirt gets 1 at the round's end, from the treasury.
#guard match next { table 3 with books := ((table 3).books.postAll [⟨.player 1, .treasury, "dirt", 1, .trade⟩]).getD (table 3).books } with
  | some s => holds s 1 "dirt" == 1 && s.balance .treasury "dirt" == 2
  | none => false

/-! ## The heat -/

-- The first roll sweeps all the dirt from the bank to the treasury, so nobody can buy it from the bank.
-- With no racket running, the reward does not grow.
#guard match next { fresh with phase := .actions } with
  | some s => s.balance .bank "dirt" == 0 && s.balance .treasury "dirt" == 6 && reward s == 0
  | none => false

/-- A seat with a front and the goods for a racket, after the first roll. -/
def building : St :=
  match next { fresh with phase := .actions, pieces := [⟨1, "front", .spot (spotOf 0)⟩] } with
  | some s => give s 1 [("wine", 2), ("fish", 1)]
  | none => fresh

-- A new racket gives no dirt at once, so a seat cannot build one and talk in the same turn. Building it
-- adds nothing to the reward.
#guard match step game building (.move 1 (.place "racket" (.spot (spotOf 0)))) with
  | .ok s => reward s == 0 && holds s 1 "dirt" == 0 && rackets s 1 == 1
  | .error _ => false

/-- Seats 0 and 1 run two more rackets each, so twelve run in all. -/
def busy : List Piece :=
  family ++ [0, 1].flatMap fun p =>
    [⟨p, "front", .spot (spotOf (10 + 2 * p))⟩, ⟨p, "racket", .spot (spotOf (10 + 2 * p))⟩,
     ⟨p, "front", .spot (spotOf (11 + 2 * p))⟩, ⟨p, "racket", .spot (spotOf (11 + 2 * p))⟩]

-- Twelve rackets running make the reward grow by 3 on a roll.
#guard match next { fund (table 0) 0 with pieces := busy } with
  | some s => reward s == 23
  | none => false

end Charter.Games.Omerta.Tests
