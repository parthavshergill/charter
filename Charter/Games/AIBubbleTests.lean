import Charter.Engine
import Charter.Games.AIBubble

/-!
# The AI Bubble, played

This plays each founding law through `Engine.step`, on tables built by hand with the pieces and hands each
test needs. Whole games are in `scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.AIBubble.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh (seats : Nat := 4) : St := initialState game seats 1 [2]

def noRegion : Region := ⟨"", 0, []⟩
def cornerOf (i j : Nat) : Nat := ((game.map.regions.getD i noRegion).spots).getD j 0
def labOf (seat : Seat) : Nat := cornerOf (seat * 4) 0

/-- Each seat has one datacenter, on a corner far from the others. -/
def labs : List Piece := [0, 1, 2, 3].map fun p => ⟨p, "datacenter", .spot (labOf p)⟩

def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

def table (pieces : List Piece := labs) : St :=
  { fresh with phase := .actions, pieces := pieces }

/-- Put this much on the bubble. -/
def onBubble (s : St) (n : Nat) : St :=
  { s with books := (s.books.postAll [⟨.bank, .treasury, "bubble", n, .trade⟩]).getD s.books }

/-- The next roll is this number. -/
def rolling (s : St) (r : Nat) : St :=
  { s with rollsMade := ((List.range 500).find? (fun k => rollAt game s.seed k == r)).getD 0 }

def afterTurn (s : St) : Option St := (step game s .forceEndTurn).toOption
def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r
def bubbleOf (s : St) : Nat := s.balance .treasury "bubble"

/-- Four turn ends: the round ends, and the next one starts with a roll of this number. -/
def afterRound (s : St) (r : Nat) : Option St := do
  let s1 ← afterTurn (rolling s 3)
  let s2 ← afterTurn (rolling s1 3)
  let s3 ← afterTurn (rolling s2 3)
  afterTurn (rolling s3 r)

/-! ## The founding laws, played -/

#guard foundingLaws.length == 4 && game.rounds == 10 && game.targetPoints == 25

-- The founding laws leave room for a table's own.
#guard plannedTotal (table).laws 4 < maxPlannedTotal / 2
#guard readsTotal (table).laws 4 < maxReadsTotal / 2

/-- Everyone holds hype. Seat 0 holds the most. -/
def paper : St := give (give (give (table) 0 [("hype", 9)]) 1 [("hype", 3)]) 2 [("hype", 1)]

-- Hype is worth a point each: a datacenter's point and 9 for the hype.
#guard paper.pointsOf 0 == 10

-- With no bubble, no roll pops it.
#guard match afterTurn (rolling paper 12) with
  | some s => holds s 0 "hype" == 9 && holds s 1 "hype" == 3
  | none => false

-- At a bubble of 24, an 11 does not pop it and a 12 does. All hype goes, and the bubble empties.
#guard match afterTurn (rolling (onBubble paper 24) 11) with
  | some s => holds s 0 "hype" == 9 && bubbleOf s == 24
  | none => false
#guard match afterTurn (rolling (onBubble paper 24) 12) with
  | some s => holds s 0 "hype" == 0 && holds s 1 "hype" == 0 && bubbleOf s == 0 && s.pointsOf 0 == 1
  | none => false

-- At 39, a 7 pops it. At 54, a 2 does. A roll may pay nobody and still pop it.
#guard match afterTurn (rolling (onBubble paper 39) 7) with
  | some s => holds s 0 "hype" == 0
  | none => false
#guard match afterTurn (rolling (onBubble paper 38) 7) with
  | some s => holds s 0 "hype" == 9
  | none => false
#guard match afterTurn (rolling (onBubble paper 54) 2) with
  | some s => holds s 0 "hype" == 0
  | none => false

-- A crash takes no capital and no pieces.
#guard match afterTurn (rolling (onBubble (give paper 0 [("capital", 5)]) 54) 2) with
  | some s => holds s 0 "capital" == 5 && s.countOf 0 "datacenter" == 1
  | none => false

/-! ## Building and raising -/

/-- A corner two steps from seat 0's datacenter. -/
def secondSite : Nat :=
  let v := labOf 0
  let w := ((fresh).neighbours v).getD 0 0
  let u := ((fresh).neighbours w).getD 0 0
  if u == v then ((fresh).neighbours w).getD 1 0 else u

/-- Seat 0 can pay for a datacenter, and has fibre to reach a free corner. -/
def builder : St :=
  let v := labOf 0
  let w := ((fresh).neighbours v).getD 0 0
  let u := secondSite
  give { (table) with
    pieces := labs ++ [⟨0, "fibre", .link (linkEnds (v, w))⟩, ⟨0, "fibre", .link (linkEnds (w, u))⟩] }
    0 [("concrete", 1), ("silicon", 1), ("power", 1), ("capital", 2)]

-- A datacenter pays its builder 2 hype and adds 1 to the bubble.
#guard match step game builder (.move (builder.currentSeat.getD 0) (.place "datacenter" (.spot secondSite))) with
  | .ok s => holds s 0 "hype" == 2 && bubbleOf s == 1 && s.pointsOf 0 == 4 && holds s 0 "capital" == 0
  | .error _ => false

/-- Seat 0 has declared 3 and holds 2. Seat 1 has declared 2 and holds 5. Seat 2 declared nothing. -/
def raising : St :=
  let s := give (give (give (table) 0 [("hype", 2)]) 1 [("hype", 5)]) 2 [("hype", 4)]
  { s with declared := fun p r =>
      if r == "capital" then (if p == 0 then 3 else if p == 1 then 2 else 0) else 0 }

-- A raise sells what was declared, up to what is held, for twice as much capital, and it goes on the
-- bubble. Then each lab gets its hype for the round, at the bubble as it stood. At a bubble of 0, that is 1.
#guard match afterRound raising 3 with
  | some s =>
    holds s 0 "capital" == 4 && holds s 0 "hype" == 1 &&
    holds s 1 "capital" == 4 && holds s 1 "hype" == 4 &&
    holds s 2 "capital" == 0 && holds s 2 "hype" == 5 &&
    bubbleOf s == 4
  | none => false

-- A bubble of 20 pays 3 hype a round.
#guard match afterRound (onBubble (table) 20) 3 with
  | some s => holds s 3 "hype" == 3
  | none => false

/-! ## The market -/

/-- Seat 0 holds 6 inference and seat 1 holds 2, so the supply is 8. -/
def selling : St := give (give (table) 0 [("inference", 6)]) 1 [("inference", 2)]

-- All of it sells. Customers pay 16 in all, split by share: a price of 2.
#guard match afterRound selling 3 with
  | some s => holds s 0 "capital" == 12 && holds s 1 "capital" == 4 && holds s 0 "inference" == 0
  | none => false

-- More supply is a lower price: 4 more tokens from a rival cuts seat 0 from 12 capital to 8.
#guard match afterRound (give selling 2 [("inference", 4)]) 3 with
  | some s => holds s 0 "capital" == 8 && holds s 1 "capital" == 2 && holds s 2 "capital" == 5
  | none => false

/-! ## Upkeep -/

/-- Seat 0 has two datacenters and holds 2 power. Seat 1 has two and holds 1. -/
def burning : St :=
  let s := give (give { (table) with pieces := labs ++ [⟨0, "datacenter", .spot secondSite⟩, ⟨1, "datacenter", .spot 20⟩] } 0 [("power", 2)]) 1 [("power", 1)]
  { s with round := 2 }

-- In round 1 nobody pays yet.
#guard match afterRound (give (table) 0 [("power", 2)]) 3 with
  | some s => holds s 0 "power" == 2
  | none => false

-- From round 2 a lab pays 1 per datacenter. A lab that is short pays what it has, and its newest goes dark.
-- A lab with no power and a single piece keeps it.
#guard match afterRound burning 3 with
  | some s =>
    holds s 0 "power" == 0 && s.countOf 0 "datacenter" == 2 &&
    holds s 1 "power" == 0 && s.countOf 1 "datacenter" == 1 &&
    s.countOf 2 "datacenter" == 1
  | none => false

end Charter.Games.AIBubble.Tests
