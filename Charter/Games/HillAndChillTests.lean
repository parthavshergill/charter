import Charter.Engine
import Charter.Games.HillAndChill

/-!
# Hill and Chill, played

Each founding law played through `Engine.step`, on a table of four friends built by hand. Whole games
are in `scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.HillAndChill.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh : St := initialState game 4 1 [2]

/-- Hand a seat some goods from the bank. -/
def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

/-- Four friends with 2 gas and 2 cash each. -/
def table : St :=
  (List.range 4).foldl (fun s p => give s p [("gas", 2), ("cash", 2)]) { fresh with phase := .actions }

/-- These seats have declared down this round. -/
def down (s : St) (ps : List Seat) : St :=
  { s with declared := fun p r => if r == "down" && ps.contains p then 1 else 0 }

def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r

/-- Every seat ends its turn, so the round ends and the next one's first roll happens. -/
def endRound (s : St) : Option St :=
  (List.range 4).foldlM (fun x _ => (step game x .forceEndTurn).toOption) s

/-- What each seat holds of a resource after the round. -/
def after (ps : List Seat) (r : Res) (s : St := table) : List Nat :=
  match endRound (down s ps) with
  | some t => [0, 1, 2, 3].map (holds t · r)
  | none => []

/-! ## The down card -/

-- After any roll, every seat holds exactly one down card, so it can declare down. This holds roll after
-- roll: an early version of the law ran the bank short on every second roll.
#guard match endRound table >>= endRound with
  | some s => [0, 1, 2, 3].all (holds s · "down" == 1)
  | none => false

-- A seat that was given a second card gives it back at the next roll.
#guard match (step game (give table 0 [("down", 2)]) .forceEndTurn).toOption with
  | some s => holds s 0 "down" == 1
  | none => false

/-! ## Lore and clout are not for sale -/

-- From the first roll the treasury holds them, so the bank has none to sell.
#guard match (step game table .forceEndTurn).toOption with
  | some s => s.balance .bank "lore" == 0 && s.balance .bank "clout" == 0 && s.balance .treasury "lore" == 160
  | none => false

/-! ## Dinner happens -/

-- Three of four are down: more than half. Each of them pays 1 gas and gets 3 lore. Seat 3 could be down,
-- keeps its gas, and gets 1 clout.
#guard after [0, 1, 2] "lore" == [3, 3, 3, 0]
#guard after [0, 1, 2] "gas" == [1, 1, 1, 2]
#guard after [0, 1, 2] "clout" == [0, 0, 0, 1]
#guard after [0, 1, 2] "cash" == [2, 2, 2, 2]

-- Everyone is down: everyone eats, but the 9 lore are shared four ways, 2 each. So one more guest costs
-- the other three a lore each, and nobody gets clout.
#guard after [0, 1, 2, 3] "lore" == [2, 2, 2, 2]
#guard after [0, 1, 2, 3] "clout" == [0, 0, 0, 0]

/-! ## Dinner falls through -/

-- Two of four is only half. The two who were down pay the ride and the no-show fee, and get no lore.
-- The other two collect clout.
#guard after [0, 1] "lore" == [0, 0, 0, 0]
#guard after [0, 1] "gas" == [1, 1, 2, 2]
#guard after [0, 1] "cash" == [1, 1, 2, 2]
#guard after [0, 1] "clout" == [0, 0, 1, 1]
#guard match endRound (down table [0, 1]) with
  | some s => s.balance .treasury "cash" == 2
  | none => false

-- Nobody is down: nobody pays, and everyone gets clout.
#guard after [] "clout" == [1, 1, 1, 1]
#guard after [] "gas" == [2, 2, 2, 2]

/-! ## No gas, no problem: someone gives you a ride -/

/-- Seat 2 has no gas. -/
def noRide : St := { table with books := (table.books.postAll [⟨.player 2, .bank, "gas", 2, .trade⟩]).getD table.books }

-- Seat 2 says down with no gas. It still counts, dinner happens, and it pays no gas for the ride.
#guard after [0, 1, 2] "lore" noRide == [3, 3, 3, 0]
#guard after [0, 1, 2] "gas" noRide == [1, 1, 0, 2]

-- When dinner falls through, a seat with no gas still pays the no-show fee.
#guard after [1, 2] "cash" noRide == [2, 1, 1, 2]

/-! ## The score -/

-- Lore and clout are each worth a point in the hand.
#guard match endRound (down table [0, 1, 2]) with
  | some s => [0, 1, 2, 3].map (s.tokenPointsOf ·) == [3, 3, 3, 1]
  | none => false

end Charter.Games.HillAndChill.Tests
