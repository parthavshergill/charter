import Charter.Engine
import Charter.Games.StrikeTheEarth

/-!
# Strike the Earth, played

Each founding law, played through `Engine.step` on a table built by hand. Whole games are in
`scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.StrikeTheEarth.Tests

open Charter Charter.Engine

abbrev St := State game

def fresh : St := initialState game 4 1 [2]

/-- No region, for reading past the end of the list. -/
def noRegion : Region := ⟨"", 0, []⟩

/-- A corner of the `i`th producing tile. -/
def cornerOf (i j : Nat) : Nat := ((game.map.regions.getD i noRegion).spots).getD j 0

/-- Corners far apart, one for each seat. -/
def homeOf (seat : Seat) : Nat := cornerOf (seat * 4) 0

def hall (p : Seat) (v : Nat := homeOf p) : Piece := ⟨p, "hall", .spot v⟩
def on (p : Seat) (k : PieceKind) (v : Nat := homeOf p) : Piece := ⟨p, k, .spot v⟩
def tunnelOf (p : Seat) (i : Nat) : Piece := ⟨p, "tunnel", .link (links.getD (p * 20 + i) (0, 1))⟩

def table (pieces : List Piece := [0, 1, 2, 3].map (hall ·)) : St :=
  { fresh with phase := .actions, pieces := pieces }

/-- Hand an account some goods from the bank. -/
def give (s : St) (a : Account) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, a, x.1, x.2, .trade⟩)).getD s.books }

def withDanger (s : St) (n : Nat) : St := give s .treasury [("danger", n)]

/-- The next roll is this number. -/
def rolling (s : St) (r : Nat) : St :=
  { s with rollsMade := ((List.range 500).find? (fun k => rollAt game s.seed k == r)).getD 0 }

def afterTurn (s : St) : Option St := (step game s .forceEndTurn).toOption
def renownOf (s : St) (p : Seat) : Nat := s.balance (.player p) "renown"
def dangerOf (s : St) : Nat := s.balance .treasury "danger"
def build (s : St) (k : PieceKind) (v : Nat := homeOf 0) : Option St :=
  (step game s (.move 0 (.place k (.spot v)))).toOption

-- The map: every number but 2, 7 and 12, and no 6 or 8 touching another.
#guard hexes.length == 17 && tiles.length == 17
#guard !tileNumbers.contains 2 && !tileNumbers.contains 7 && !tileNumbers.contains 12
#guard tiles.all fun a => tiles.all fun b =>
  !(a.hex.neighbors).contains b.hex ||
    (a.number != b.number && !([some 6, some 8].contains a.number && [some 6, some 8].contains b.number))

-- Deeds pay renown, and renown is the score: a seat's points are what it holds.
#guard match build (give table (.player 0) [("ore", 2), ("ember", 2)]) "workshop" with
  | some s => renownOf s 0 == 2 && s.pointsOf 0 == 2 && dangerOf s == 0
  | none => false

-- A shaft pays 1 renown and raises the danger by 2.
#guard match build (give table (.player 0) [("ore", 2), ("stone", 1)]) "shaft" with
  | some s => renownOf s 0 == 1 && dangerOf s == 2
  | none => false

-- An epitaph costs renown and danger, and it is worth 5 points whatever else happens.
#guard match build (give table (.player 0) [("renown", 3), ("danger", 1)]) "epitaph" with
  | some s => renownOf s 0 == 1 && s.pointsOf 0 == 6
  | none => false

/-- Seat 0 has a shaft, and seat 1 has a workshop with its hall upgraded. -/
def deep : St :=
  table [hall 0, on 0 "shaft", on 1 "workshop", hall 1 (homeOf 2), hall 2 (homeOf 3), hall 3 (cornerOf 2 0)]

-- A 7 at low danger does nothing.
#guard match afterTurn (rolling (withDanger deep 2) 7) with
  | some s => s.countOf 0 "shaft" == 1 && s.countOf 1 "workshop" == 1 && renownOf s 0 == 0
  | none => false

-- A 7 at danger 3 takes the shaft and pays for it, and leaves the workshop.
#guard match afterTurn (rolling (withDanger deep 3) 7) with
  | some s => s.countOf 0 "shaft" == 0 && renownOf s 0 == 2 && s.countOf 1 "workshop" == 1 && renownOf s 1 == 0
  | none => false

-- A 7 at danger 9 takes the workshop too, and pays 3 renown for it.
#guard match afterTurn (rolling (withDanger deep 9) 7) with
  | some s => s.countOf 1 "workshop" == 0 && renownOf s 1 == 3 && s.pointsOf 1 == 3
  | none => false

/-- Each seat has a hall and two tunnels. Seat 0 has a gate, and all hold fungus. -/
def wet : St :=
  give (give (withDanger (table
      ([on 0 "gate"] ++ ([0, 1, 2, 3].flatMap fun p => [hall p, tunnelOf p 0, tunnelOf p 1]))) 6)
    (.player 0) [("fungus", 5)]) (.player 1) [("fungus", 5)]

-- A low roll takes a tunnel and half the danger in fungus from a clan with no gate, and pays it 1 renown.
#guard match afterTurn (rolling wet 3) with
  | some s =>
    s.countOf 0 "tunnel" == 2 && s.balance (.player 0) "fungus" ≥ 5 && renownOf s 0 == 0 &&
    s.countOf 1 "tunnel" == 1 && s.balance (.player 1) "fungus" ≤ 2 + 2 && renownOf s 1 == 1
  | none => false

/-- Seat 0 has two shafts and a workshop, and seat 1 has one shaft. -/
def hunted : St :=
  table [hall 0, on 0 "shaft", hall 0 (homeOf 2), on 0 "shaft" (homeOf 2), on 0 "workshop" (cornerOf 2 0), hall 1, on 1 "shaft", hall 3]

-- The Thing Below sleeps below danger 6.
#guard match afterTurn (rolling (withDanger hunted 5) 12) with
  | some s => s.countOf 0 "shaft" == 2 && renownOf s 0 == 0
  | none => false

-- At danger 6 it eats from the clan with the most shafts, and only that clan.
#guard match afterTurn (rolling (withDanger hunted 6) 12) with
  | some s =>
    s.countOf 0 "shaft" == 1 && s.countOf 0 "workshop" == 0 && renownOf s 0 == 4 &&
    s.countOf 1 "shaft" == 1 && renownOf s 1 == 0
  | none => false

-- A clan's last piece stays, and it is still paid.
#guard match afterTurn (rolling (withDanger (table [on 0 "shaft", hall 1, hall 2, hall 3]) 3) 7) with
  | some s => s.countOf 0 "shaft" == 1 && renownOf s 0 == 2
  | none => false

end Charter.Games.StrikeTheEarth.Tests
