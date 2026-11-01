import HexGrid
/-! Exhaustive executable checks on small boards (radius 0..3), with the
radius-2 board (19 hexes, 54 vertices, 72 edges) as the main case. -/
open HexGrid

namespace HexGridTests

def board := hexagon 2
def vs := verticesOf board
def es := edgesOf board

def allDistinct {α} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

-- sizes
#guard board.length == 19
#guard vs.length == 54
#guard es.length == 72
#guard (List.range 6).all fun r => (hexagon r).length == 3 * r * r + 3 * r + 1
#guard (List.range 6).all fun r => allDistinct (hexagon r)
#guard (List.range 6).all fun r => (verticesOf (hexagon r)).length == 6 * (r + 1) * (r + 1)
#guard (List.range 6).all fun r => (edgesOf (hexagon r)).length == 9 * r * r + 15 * r + 6

-- hexagon membership agrees with dist on the square [-4,4]^2
def square (n : Nat) : List Hex :=
  (List.range (2*n+1)).flatMap fun (i : Nat) => (List.range (2*n+1)).map fun (j : Nat) =>
    ⟨(i : Int) - n, (j : Int) - n⟩
#guard (List.range 4).all fun r => (square 4).all fun h =>
  (hexagon r).contains h == decide (h.dist Hex.origin ≤ r)

-- every hex has 6 distinct vertices / edges / neighbours
#guard board.all fun h => allDistinct h.vertices && allDistinct h.edges && allDistinct h.neighbors

-- canonical forms agree: v ∈ h.vertices ↔ h ∈ v.hexes (over board × a wider vertex set)
def wide := hexagon 4
def wideVs := verticesOf wide
def wideEs := edgesOf wide
#guard board.all fun h => wideVs.all fun v => h.vertices.contains v == v.hexes.contains h
#guard board.all fun h => wideEs.all fun e => h.edges.contains e == e.hexes.contains h

-- vertex shared by exactly 3 distinct hexes, edge by exactly 2 (counted by enumeration)
#guard vs.all fun v => (wide.filter fun h => h.vertices.contains v).length == 3
#guard es.all fun e => (wide.filter fun h => h.edges.contains e).length == 2

-- edges of a vertex are exactly the edges having it as an endpoint
#guard vs.all fun v => wideEs.all fun e => v.edges.contains e == (e.ends.1 == v || e.ends.2 == v)
-- adjacent vertices are exactly the other ends of its edges
#guard vs.all fun v => wideVs.all fun w =>
  v.adjacentVertices.contains w == v.edges.any fun e =>
    (e.ends.1 == v && e.ends.2 == w) || (e.ends.2 == v && e.ends.1 == w)
#guard vs.all fun v => allDistinct v.adjacentVertices && allDistinct v.edges && allDistinct v.hexes
#guard vs.all fun v => v.adjacentVertices.all fun w => w.adjacentVertices.contains v
-- an edge's hexes are those shared by both ends
#guard es.all fun e => e.hexes.all fun h => e.ends.1.hexes.contains h && e.ends.2.hexes.contains h
#guard es.all fun e => (e.ends.1.hexes.filter fun h => e.ends.2.hexes.contains h).length == 2
-- an edge's two ends are both vertices of each of its hexes
#guard es.all fun e => e.hexes.all fun h => h.vertices.contains e.ends.1 && h.vertices.contains e.ends.2
-- the hexes of an edge are neighbours
#guard es.all fun e => match e.hexes with | [a, b] => a.neighbors.contains b | _ => false

-- vertex degree within the radius-2 board: 3a + 2b = 2 * 72, a + b = 54
#guard (vs.filter fun v => (v.edges.filter es.contains).length == 3).length == 36
#guard (vs.filter fun v => (v.edges.filter es.contains).length == 2).length == 18

-- distance
#guard board.all fun a => board.all fun b => a.dist b == b.dist a
#guard board.all fun a => a.neighbors.all fun b => a.dist b == 1
#guard board.all fun a => board.all fun b => board.all fun c => a.dist c ≤ a.dist b + b.dist c
#guard (Hex.mk 2 (-1)).dist (Hex.mk (-2) 1) == 4

-- pixels: vertices of a hex sit at distance `size` from its centre,
-- and a shared vertex has the same pixel from every hex (canonical!)
def close (a b : Float × Float) : Bool := (a.1 - b.1).abs < 1e-9 && (a.2 - b.2).abs < 1e-9
def cornerPixel (h : Hex) (i : Nat) : Float × Float :=
  let (x, y) := h.toPixel 1.0
  let ang := (60.0 * i.toFloat - 90.0) * 3.141592653589793 / 180.0
  (x + Float.cos ang, y + Float.sin ang)
#guard board.all fun h => (List.range 6).all fun i =>
  close (cornerPixel h i) ((h.vertices.getD i default).toPixel 1.0)
#guard es.all fun e =>
  let m := e.toPixel 1.0
  let a := e.ends.1.toPixel 1.0
  let b := e.ends.2.toPixel 1.0
  close m ((a.1 + b.1) / 2.0, (a.2 + b.2) / 2.0)

end HexGridTests
