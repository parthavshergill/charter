import Charter.Engine
import Charter.Games.ThePit

/-!
# The Pit, played

This plays each founding law, and a future, through `Engine.step`, on tables built by hand with the hands
each test needs. Whole games are in `scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.ThePit.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh (seats : Nat := 4) : St := initialState game seats 1 [2]

def noRegion : Region := ⟨"", 0, []⟩
def cornerOf (i j : Nat) : Nat := ((game.map.regions.getD i noRegion).spots).getD j 0
def farmOf (seat : Seat) : Nat := cornerOf (seat * 4) 0

/-- Each seat has one farm, on a corner far from the others. -/
def farms : List Piece := [0, 1, 2, 3].map fun p => ⟨p, "farm", .spot (farmOf p)⟩

def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

/-- A table in play, with the memberships on the secretary's desk, as after the first roll. -/
def table : St :=
  let s : St := { fresh with phase := .actions, pieces := farms }
  { s with books := (s.books.postAll [⟨.bank, .treasury, "membership", 10, .trade⟩]).getD s.books }

/-- The next roll is this number. -/
def rolling (s : St) (r : Nat) : St :=
  { s with rollsMade := ((List.range 500).find? (fun k => rollAt game s.seed k == r)).getD 0 }

def afterTurn (s : St) : Option St := (step game s .forceEndTurn).toOption
def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r

/-- Four turn ends: the round ends. The dice show 7 throughout, which pays nobody here. -/
def afterRound (s : St) : Option St := do
  let s1 ← afterTurn (rolling s 7)
  let s2 ← afterTurn (rolling s1 7)
  let s3 ← afterTurn (rolling s2 7)
  afterTurn (rolling s3 7)

/-- Seats declare these bids in gold. -/
def bidding (s : St) (bids : List (Seat × Nat)) : St :=
  { s with declared := fun p r => if r == "gold" then ((bids.find? (·.1 == p)).map (·.2)).getD 0 else 0 }

/-! ## The founding laws, in place -/

#guard foundingLaws.length == 3 && game.rounds == 10 && game.targetPoints == 24

-- The founding laws leave room for a table's own.
#guard plannedTotal (table).laws 4 < maxPlannedTotal / 2
#guard readsTotal (table).laws 4 < maxReadsTotal / 2

-- A membership is worth 3 points, and a farm 1.
#guard (give { fresh with phase := .actions, pieces := farms } 0 [("membership", 2)]).pointsOf 0 == 7

/-! ## The spot market -/

/-- Seat 0 holds 3 wheat and seat 1 holds 1, in round 1. The pot is 6. -/
def selling : St := give (give (table) 0 [("wheat", 3)]) 1 [("wheat", 1)]

-- All of it sells, split by share and rounded down: 6 × 3 / 4 is 4, and 6 × 1 / 4 is 1.
#guard match afterRound selling with
  | some s => holds s 0 "gold" == 4 && holds s 1 "gold" == 1 && holds s 0 "wheat" == 0 && holds s 1 "wheat" == 0
  | none => false

-- The pot grows by 2 a round: in round 5 it is 14, so the same hands get 10 and 3.
#guard match afterRound { selling with round := 5 } with
  | some s => holds s 0 "gold" == 10 && holds s 1 "gold" == 3
  | none => false

-- One lone wheat takes the whole pot.
#guard match afterRound (give (table) 2 [("wheat", 1)]) with
  | some s => holds s 2 "gold" == 6
  | none => false

-- More wheat is a lower price: 4 more from a rival cuts seat 0 from 4 gold to 2.
#guard match afterRound (give selling 2 [("wheat", 4)]) with
  | some s => holds s 0 "gold" == 2 && holds s 2 "gold" == 3
  | none => false

-- With no wheat anywhere, nobody is paid.
#guard match afterRound (table) with
  | some s => [0, 1, 2, 3].all fun p => holds s p "gold" == 0
  | none => false

/-! ## The bumper crop -/

-- Seat 0's farm stands on the wheat hex numbered 6. A 6 pays it 1 wheat, and the bank pays it 1 more.
#guard (game.map.regions.getD 0 noRegion).res == "wheat" && (game.map.regions.getD 0 noRegion).number == 6
#guard match afterTurn (rolling (table) 6) with
  | some s => holds s 0 "wheat" == 2
  | none => false

-- Other goods are not doubled: seat 1's farm on the lumber hex numbered 8 gets 1 lumber.
#guard (game.map.regions.getD 4 noRegion).res == "lumber" && (game.map.regions.getD 4 noRegion).number == 8
#guard match afterTurn (rolling (table) 8) with
  | some s => holds s 1 "lumber" == 1
  | none => false

/-! ## The auction -/

/-- Seat 0 bids 9 and holds 10. Seat 1 bids 5 and holds 20. Seat 2 bids 12 but holds only 4, so its bid
counts 4. -/
def auction : St :=
  bidding (give (give (give (table) 0 [("gold", 10)]) 1 [("gold", 20)]) 2 [("gold", 4)]) [(0, 9), (1, 5), (2, 12)]

-- The highest bid wins one membership and pays 1 more than the next-highest bid: 6, not 9.
#guard match afterRound auction with
  | some s =>
    holds s 0 "membership" == 1 && holds s 0 "gold" == 4 && s.pointsOf 0 == 4 &&
    holds s 1 "membership" == 0 && holds s 1 "gold" == 20 &&
    holds s 2 "membership" == 0 && holds s 2 "gold" == 4 &&
    s.balance .treasury "membership" == 9
  | none => false

-- The spec rejects the wrong outcomes: the loser does not get it, and the winner does not pay its own bid.
#guard match afterRound auction with
  | some s => !(holds s 1 "membership" == 1) && !(holds s 0 "gold" == 1)
  | none => false

-- A lone bidder pays 1.
#guard match afterRound (bidding (give (table) 3 [("gold", 7)]) [(3, 7)]) with
  | some s => holds s 3 "membership" == 1 && holds s 3 "gold" == 6
  | none => false

-- A tie at the top sells nothing, and nobody pays.
#guard match afterRound (bidding (give (give (table) 0 [("gold", 5)]) 1 [("gold", 5)]) [(0, 5), (1, 5)]) with
  | some s => holds s 0 "membership" == 0 && holds s 1 "membership" == 0 && holds s 0 "gold" == 5 && holds s 1 "gold" == 5
  | none => false

-- An unsold lot rolls over: after a tie in round 1, a lone bid of 3 in round 2 buys 2 memberships, for 1.
#guard match (afterRound (bidding (give (give (table) 0 [("gold", 5)]) 1 [("gold", 5)]) [(0, 5), (1, 5)])).bind
    (fun s => afterRound (bidding s [(0, 3)])) with
  | some s => holds s 0 "membership" == 2 && holds s 0 "gold" == 4 && s.balance .treasury "membership" == 8
  | none => false

-- In round 10, every membership left on the desk is sold.
#guard match afterRound (bidding (give { (table) with round := 10 } 2 [("gold", 4)]) [(2, 4)]) with
  | some s => holds s 2 "membership" == 10 && s.balance .treasury "membership" == 0
  | none => false

-- Bids clear when the round ends.
#guard match afterRound auction with
  | some s => s.declared 0 "gold" == 0
  | none => false

-- The bank never sells a membership: they are on the secretary's desk.
#guard (step game (give (table) 0 [("gold", 3)]) (.move 0 (.bankTrade "gold" "membership"))).toOption.isNone

/-! ## A future -/

/-- Seat 0 sells seat 1 one wheat a round for 2 rounds, at 3 gold a round. Both put up everything. -/
def future : Deal :=
  { title := "Wheat future", signers := [0, 1], rounds := 2, exitNotice := 2
    deposits := [(0, "wheat", 2), (1, "gold", 6)]
    terms := [.everyRound [⟨0, .seat 1, "wheat", 1⟩, ⟨1, .seat 0, "gold", 3⟩]] }

/-- The future is proposed and signed. Seat 0 held 2 wheat and seat 1 held 10 gold. -/
def signed : Option St := do
  let s := give (give (table) 0 [("wheat", 2)]) 1 [("gold", 10)]
  let id := s.nextProposalId
  let s ← (step game s (.propose 0 (.deal future))).toOption
  let s ← (step game s (.sign 0 id)).toOption
  (step game s (.sign 1 id)).toOption

-- The deposits leave both hands at once.
#guard match signed with
  | some s => s.deals.length == 1 && holds s 0 "wheat" == 0 && holds s 1 "gold" == 4
  | none => false

-- A seller without the wheat cannot sign: nobody can sell what they do not have.
#guard match (do
    let s := give (table) 1 [("gold", 10)]
    let id := s.nextProposalId
    let s ← (step game s (.propose 0 (.deal future))).toOption
    let s ← (step game s (.sign 1 id)).toOption
    (step game s (.sign 0 id)).toOption : Option St) with
  | some s => s.deals.isEmpty
  | none => true

-- At the round's end the deal pays first, so the wheat it delivers is sold that round. Seat 1 is the only
-- seller, so it takes the whole pot of 6. Seat 0 gets its 3 gold. The wheat still in deposit is not sold.
#guard match signed.bind afterRound with
  | some s =>
    holds s 1 "gold" == 10 && holds s 0 "gold" == 3 && holds s 1 "wheat" == 0 &&
    s.balance (.deposit 0 0) "wheat" == 1
  | none => false

-- Gold in deposit cannot bid. Seat 1 declares 9 but holds only 4 in hand, and seat 0 wins with 5.
#guard match signed.bind fun s => afterRound (bidding (give s 0 [("gold", 5)]) [(0, 5), (1, 9)]) with
  | some s => holds s 0 "membership" == 1 && holds s 1 "membership" == 0
  | none => false

-- Without the future, the same 10 gold would have won.
#guard match afterRound (bidding (give (give (table) 0 [("gold", 5)]) 1 [("gold", 10)]) [(0, 5), (1, 9)]) with
  | some s => holds s 1 "membership" == 1 && holds s 0 "membership" == 0
  | none => false

end Charter.Games.ThePit.Tests
