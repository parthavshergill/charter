import Charter.Words
import Charter.Games.HexMap

/-!
# The Island: a game on a Catan-style map

Nineteen hexes, five resources, and one desert. The map's shape comes from `lean-hexgrid`: spots are
the corners of the hexes, and links are their sides. A spot's id is its place in `spots`.
This is a game definition and not part of the spec, so it can use a package.
-/

namespace Charter.Games.Island

open HexGrid

/-- The inner hexes, then the outer hexes, in `hexagon 2` order. -/
def hexes : List Hex := hexagon 2

/-- Resources in `hexes` order, after the desert in the middle. -/
def tileResources : List Res :=
  [ "timber", "grain", "ore", "timber", "wool", "brick"
  , "ore", "wool", "grain", "timber", "brick", "wool", "grain", "ore", "timber", "brick", "grain", "wool" ]

/-- Dice numbers in `hexes` order, after the desert in the middle. -/
def tileNumbers : List Nat :=
  [ 9, 4, 5, 6, 3, 11
  , 5, 2, 6, 3, 8, 10, 9, 12, 11, 4, 8, 10 ]

/-- Every hex of the map, the desert first. -/
def tiles : List TileDef :=
  match hexes with
  | [] => []
  | center :: rest =>
    { hex := center, res := none, number := none } ::
      ((rest.zip (tileResources.zip tileNumbers)).map fun x =>
        { hex := x.1, res := some x.2.1, number := some x.2.2 })

/-- The corners of the map. A spot's id is its place in this list. -/
def spots : List Vertex := verticesOf hexes

/-- The sides of the map. A link's id is its place in this list. -/
def edges : List Edge := edgesOf hexes

/-- The id of a corner. -/
def spotId (v : Vertex) : Nat := spots.idxOf v

/-- The two spots a side joins. -/
def linkOf (e : Edge) : Nat × Nat := (spotId e.ends.1, spotId e.ends.2)

/-- The links of the map, in `edges` order. -/
def links : List (Nat × Nat) := edges.map linkOf

/-- A hex with a number produces its resource at its six corners. -/
def regionOf (t : TileDef) : Option Region :=
  match t.res, t.number with
  | some r, some n => some { res := r, number := n, spots := t.hex.vertices.map spotId }
  | _, _ => none

/-- The Island game: first to 10 points, within 30 rounds. -/
def island : GameDef where
  name := "The Island"
  resources := [⟨"grain", 30⟩, ⟨"timber", 30⟩, ⟨"ore", 30⟩, ⟨"wool", 30⟩, ⟨"brick", 30⟩]
  pieces :=
    [ { name := "road", cost := [("timber", 1), ("brick", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "settlement", cost := [("timber", 1), ("brick", 1), ("grain", 1), ("wool", 1)]
        points := 1, placement := .spot, yield := 1, limit := 5 }
    , { name := "city", cost := [("grain", 2), ("ore", 3)], points := 2
        placement := .upgrade "settlement", yield := 2, limit := 4 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := tiles.filterMap regionOf }
  diceCount := 2
  diceSides := 6
  targetPoints := 10
  rounds := 30
  bankRate := 4
  setupPieces := ["settlement", "road"]

theorem island_valid : island.Valid := by decide +kernel

/-- The map has the shape it should: 19 hexes, 54 spots, 72 links, 18 producing regions. -/
example : hexes.length = 19 ∧ spots.length = 54 ∧ links.length = 72 ∧
    island.map.regions.length = 18 := by decide +kernel

end Charter.Games.Island
