# lean-hexgrid

Name every hex, corner, and side of a pointy-top hexagonal grid exactly once, so that board games, maps, and simulations can store pieces on vertices and edges without duplicates.

## Non-goals

- No flat-top layout, no offset or doubled coordinates. Axial `(q, r)` only.
- No rendering. `toPixel` gives coordinates; drawing is the caller's job.
- No path finding, line drawing, or field of view in the library. The BFS in
  `examples/` is a usage demo.
- No Mathlib or Batteries dependency.

## Guarantees

All proved for every hex (file `HexGrid/Theorems.lean`), with no `sorry` and
no `native_decide`. The coordinate and canonical-name conventions the
statements use are in Quickstart → Coordinate convention.

Neighbours and distance:

- `neighbors_symm : b ∈ a.neighbors → a ∈ b.neighbors`
- `neighbors_nodup (h : Hex) : h.neighbors.Nodup`
- `not_mem_neighbors_self (h : Hex) : h ∉ h.neighbors`
- `dist_symm (a b : Hex) : a.dist b = b.dist a`
- `dist_self (a : Hex) : a.dist a = 0`
- `dist_eq_zero_iff {a b : Hex} : a.dist b = 0 ↔ a = b`
- `dist_triangle (a b c : Hex) : a.dist c ≤ a.dist b + b.dist c`
- `dist_eq_one_iff_mem_neighbors {a b : Hex} : a.dist b = 1 ↔ b ∈ a.neighbors`

Vertices (canonical forms agree):

- `vertex_hexes_length (v : Vertex) : v.hexes.length = 3`
- `vertex_hexes_nodup (v : Vertex) : v.hexes.Nodup`
- `vertices_nodup (h : Hex) : h.vertices.Nodup`
- `mem_vertices_iff_mem_hexes {h : Hex} {v : Vertex} : v ∈ h.vertices ↔ h ∈ v.hexes`
- `vertex_edges_nodup (v : Vertex) : v.edges.Nodup`
- `mem_vertex_edges_iff {v : Vertex} {e : Edge} : e ∈ v.edges ↔ e.HasEnd v`
- `adjacentVertices_nodup (v : Vertex) : v.adjacentVertices.Nodup`
- `adjacent_symm {v w : Vertex} : w ∈ v.adjacentVertices → v ∈ w.adjacentVertices`
- `not_adjacent_self (v : Vertex) : v ∉ v.adjacentVertices`
- `mem_adjacentVertices_iff {v w : Vertex} : w ∈ v.adjacentVertices ↔ ∃ e : Edge, e.ends = (v, w) ∨ e.ends = (w, v)`

Edges:

- `edges_nodup (h : Hex) : h.edges.Nodup`
- `edge_hexes_length (e : Edge) : e.hexes.length = 2`
- `mem_edges_iff_mem_hexes {h : Hex} {e : Edge} : e ∈ h.edges ↔ h ∈ e.hexes`
- `edge_ends_ne (e : Edge) : e.ends.1 ≠ e.ends.2`
- `mem_edge_hexes_iff {e : Edge} {h : Hex} : h ∈ e.hexes ↔ h ∈ e.ends.1.hexes ∧ h ∈ e.ends.2.hexes`
- `edge_hexes_neighbors (e : Edge) : ∃ a b, e.hexes = [a, b] ∧ b ∈ a.neighbors`
- `edge_ends_mem_vertices {e : Edge} {h : Hex} (he : h ∈ e.hexes) : e.ends.1 ∈ h.vertices ∧ e.ends.2 ∈ h.vertices`

Boards:

- `hexagon_length (r : Nat) : (hexagon r).length = 3 * r * r + 3 * r + 1`
- `mem_hexagon_iff {r : Nat} {h : Hex} : h ∈ hexagon r ↔ h.dist origin ≤ r`
- `hexagon_nodup (r : Nat) : (hexagon r).Nodup`
- `mem_verticesOf {hs : List Hex} {v : Vertex} : v ∈ verticesOf hs ↔ ∃ h ∈ hs, h ∈ v.hexes`
- `verticesOf_nodup (hs : List Hex) : (verticesOf hs).Nodup`
- `mem_edgesOf {hs : List Hex} {e : Edge} : e ∈ edgesOf hs ↔ ∃ h ∈ hs, h ∈ e.hexes`
- `edgesOf_nodup (hs : List Hex) : (edgesOf hs).Nodup`

Kernel-checked with `decide` (file `Tests/HexGridTests/Kernel.lean`):
`(verticesOf (hexagon 2)).length = 54`, `(edgesOf (hexagon 2)).length = 72`,
the same for radius 3 (96 and 132), and every vertex of the radius-2 board
has all 3 hexes inside radius 3.

Axiom audit (`lake env lean HexGrid/Audit.lean`): every theorem above depends
on a subset of `[propext, Classical.choice, Quot.sound]`;
`vertex_hexes_length` and `edge_hexes_length` depend on no axioms.

## What is tested but not proved

`Tests/HexGridTests/Board.lean` (`#guard`, evaluated at build time) checks:

- `verticesOf (hexagon r)` and `edgesOf (hexagon r)` have `6(r+1)²` and
  `9r² + 15r + 6` elements for radius 0..5. (The general count formula is
  not proved; radius 2 and 3 are also kernel-checked. Membership and
  no-duplicates are proved for every board.)
- On the radius-2 board against all vertices/edges of radius 4: each vertex
  is a corner of exactly 3 hexes and each edge a side of exactly 2.
- Vertex degree inside the radius-2 board: 36 vertices of degree 3, 18 of
  degree 2.
- Pixel geometry: the `i`-th entry of `h.vertices` sits at angle
  `60°·i − 90°` from the hex centre at distance `size`; `Edge.toPixel` is the
  midpoint of its ends. Floats are not reasoned about in proofs.

## Quickstart

### Coordinate convention

Axial `(q, r)`, pointy-top. Screen `x` grows east, screen `y` grows south. The
cube coordinate `s = -q - r` is implicit.

```
                       N corner
                          *
                         / \
               NW side  /   \  NE side
                       /     \
            NW corner *       * NE corner
                      |       |
               W side | (q,r) | E side
                      |       |
            SW corner *       * SE corner
                       \     /
               SW side  \   /  SE side
                         \ /
                          *
                       S corner

   neighbours:  NW = (q, r-1)     NE = (q+1, r-1)
                W  = (q-1, r)     E  = (q+1, r)
                SW = (q-1, r+1)   SE = (q, r+1)
```

Canonical names:

| Thing | Canonical form | The other names it has |
|---|---|---|
| vertex | `⟨h, .n⟩` (top corner) or `⟨h, .s⟩` (bottom corner) | `NE` corner of `h` = `⟨h.northEast, .s⟩`; `SE` = `⟨h.southEast, .n⟩`; `SW` = `⟨h.southWest, .n⟩`; `NW` = `⟨h.northWest, .s⟩` |
| edge | `⟨h, .ne⟩`, `⟨h, .e⟩`, `⟨h, .se⟩` | `SW` side of `h` = `⟨h.southWest, .ne⟩`; `W` = `⟨h.west, .e⟩`; `NW` = `⟨h.northWest, .se⟩` |

Every vertex is shared by 3 hexes, every edge by 2. Because each vertex and
edge has exactly one canonical value, `DecidableEq` on `Vertex` and `Edge` is
geometric equality.

API (namespace `HexGrid`): `Hex`, `Corner`, `Vertex`, `Side`, `Edge`,
`Hex.neighbors`, `Hex.dist`, `Hex.vertices`, `Hex.edges`, `Vertex.hexes`,
`Vertex.adjacentVertices`, `Vertex.edges`, `Edge.ends`, `Edge.hexes`,
`Edge.HasEnd`, `Edge.IsAdjacent`, `ring`, `hexagon`, `verticesOf`, `edgesOf`,
`Hex.toPixel`, `Vertex.toPixel`, `Edge.toPixel` (midpoint). All types derive
`DecidableEq, Hashable, Repr, Ord, Inhabited`.

### Using it

`lakefile.toml`:

```toml
[[require]]
name = "hexgrid"
path = "../lean-hexgrid"
```

```lean
import HexGrid
open HexGrid

def board : List Hex := hexagon 2                 -- 19 hexes
def spots : List Vertex := verticesOf board        -- 54 settlement spots
def roads : List Edge := edgesOf board             -- 72 road spots

-- distance rule: no building on v or an adjacent vertex
def free (taken : List Vertex) (v : Vertex) : Bool :=
  !taken.contains v && v.adjacentVertices.all (!taken.contains ·)

#eval (Hex.mk 0 0).vertices
#eval (Vertex.mk ⟨0, 0⟩ .n).hexes      -- [⟨0,0⟩, ⟨0,-1⟩, ⟨1,-1⟩]
#eval (Edge.mk ⟨0, 0⟩ .e).ends
```

Build and test: `lake build` (builds the library, the `#guard` and `decide`
tests, the audit, and the demo).

## Second use case

Shortest paths for a field robot on a hex survey map with a wall of blocked
cells: breadth-first search over `Hex.neighbors`, an ASCII map, and a check
that every path length is at least `Hex.dist`. File `examples/MapDemo.lean`,
run with `lake exe hexgrid-demo`:

```
Survey area: 61 cells, 7 blocked
BFS distances from base { q := -2, r := 0 }:
          4   4   5   6   7
        3   3  ##   6   7   8
      2   2   2  ##   7   8   9
    2   1   1   2  ##   8   8   8
  2   1   0   1   2  ##   7   7   8
    2   1   1   2   3  ##   6   7
      2   2   2  ##   4   5   6
        3   3  ##   5   5   6
          4   4   5   6   6
Reachable cells: 54
Straight-line distance base→goal: 5
Path length around the wall:      8
BFS ≥ hex distance everywhere: true
```
