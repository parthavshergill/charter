import Charter.Words
import Charter.Games.HexMap

/-!
# The Belt: a small game among the asteroids

A second game, to show that a game is data. It has four resources, not five, and other pieces: lanes,
outposts, stations and docks. Its map is a star of thirteen hexes, and it uses two four-sided dice. It
is first to 8 points, within 20 rounds. It is a game definition and not part of the spec.
-/

namespace Charter.Games.Belt

open HexGrid

/-- The hub in the middle, the six hexes around it, and every second hex of the next ring. -/
def hexes : List Hex :=
  [Hex.origin] ++ ring 1 ++ (ring 2).zipIdx.filterMap fun (h, i) => if i % 2 == 0 then some h else none

def tileResources : List Res :=
  ["ice", "helium", "alloy", "crystal", "ice", "alloy", "helium", "ice", "alloy", "helium", "crystal", "alloy"]

def tileNumbers : List Nat :=
  [5, 4, 6, 3, 5, 7, 4, 6, 3, 5, 7, 2]

/-- Every hex of the map, the hub first. -/
def tiles : List TileDef :=
  match hexes with
  | [] => []
  | center :: rest =>
    { hex := center, res := none, number := none } ::
      ((rest.zip (tileResources.zip tileNumbers)).map fun x =>
        { hex := x.1, res := some x.2.1, number := some x.2.2 })

def spots : List Vertex := spotsOf tiles
def edges : List Edge := sidesOf tiles
def links : List (Nat × Nat) := linksOf tiles

/-- The Belt: first to 8 points, within 20 rounds. -/
def belt : GameDef where
  name := "The Belt"
  resources := [⟨"helium", 24⟩, ⟨"alloy", 24⟩, ⟨"ice", 24⟩, ⟨"crystal", 24⟩]
  pieces :=
    [ { name := "lane", cost := [("alloy", 1)], points := 0
        placement := .link, yield := 0, limit := 12 }
    , { name := "outpost", cost := [("helium", 1), ("alloy", 1), ("ice", 1)], points := 1
        placement := .spot, yield := 1, limit := 5 }
    , { name := "station", cost := [("helium", 2), ("crystal", 2)], points := 2
        placement := .upgrade "outpost", yield := 2, limit := 3 }
    , { name := "dock", cost := [("ice", 2), ("crystal", 1)], points := 1
        placement := .attach "outpost", yield := 0, limit := 2 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 4
  targetPoints := 8
  rounds := 20
  bankRate := 3
  setupPieces := ["outpost", "lane"]

theorem belt_valid : belt.Valid := by decide +kernel

/-- The map has the shape it should: 13 hexes and 12 producing regions. -/
example : hexes.length = 13 ∧ belt.map.regions.length = 12 := by decide +kernel

end Charter.Games.Belt
