import Charter.Words
import HexGrid

/-!
# A game's map, made of hexes

A list of hexes gives a map: spots are the corners of the hexes, and links are their sides. A spot's
id is its place in `spots`. A game definition does not need a hex map, but the games the server can
draw have one.
-/

namespace Charter.Games

open HexGrid

/-- One hex of the map. A hex with no resource and no number produces nothing. -/
structure TileDef where
  hex : Hex
  res : Option Res
  number : Option Nat
  deriving Repr, Inhabited

/-- The corners of these tiles. -/
def spotsOf (ts : List TileDef) : List Vertex := verticesOf (ts.map (·.hex))

/-- The sides of these tiles. -/
def sidesOf (ts : List TileDef) : List Edge := edgesOf (ts.map (·.hex))

/-- The two spots each side joins. -/
def linksOf (ts : List TileDef) : List (Nat × Nat) :=
  let vs := spotsOf ts
  (sidesOf ts).map fun e => (vs.idxOf e.ends.1, vs.idxOf e.ends.2)

/-- A hex with a resource and a number produces at its six corners. -/
def regionsOf (ts : List TileDef) : List Region :=
  let vs := spotsOf ts
  ts.filterMap fun t =>
    match t.res, t.number with
    | some r, some n => some { res := r, number := n, spots := t.hex.vertices.map vs.idxOf }
    | _, _ => none

end Charter.Games
