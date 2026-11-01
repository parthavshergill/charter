/-!
# HexGrid.Basic

Axial coordinates for a pointy-top hexagonal grid, with canonical names for
the vertices (corners) and edges (sides) shared between hexes.

Conventions (see README for a diagram):

* A hex is `⟨q, r⟩` in axial coordinates. The implicit third cube
  coordinate is `s = -q - r`.
* Hexes are pointy-top. Screen `x` grows to the east, screen `y` grows to the
  south. `q` grows to the east, `r` grows to the south-east.
* The six neighbours of `⟨q, r⟩` are
  `E = ⟨q+1, r⟩`, `NE = ⟨q+1, r-1⟩`, `NW = ⟨q, r-1⟩`,
  `W = ⟨q-1, r⟩`, `SW = ⟨q-1, r+1⟩`, `SE = ⟨q, r+1⟩`.
* Every vertex touches three hexes. Its canonical name is the unique hex for
  which it is the top (`n`) or bottom (`s`) corner.
* Every edge touches two hexes. Its canonical name is the unique hex for
  which it is the north-east (`ne`), east (`e`), or south-east (`se`) side.
-/

namespace HexGrid

/-- A hex in axial coordinates (pointy-top). -/
structure Hex where
  q : Int
  r : Int
  deriving DecidableEq, Hashable, Repr, Ord, Inhabited

/-- The two canonical corners of a pointy-top hex: top and bottom. -/
inductive Corner
  | n
  | s
  deriving DecidableEq, Hashable, Repr, Ord, Inhabited

/-- A vertex, named by the hex whose top (`n`) or bottom (`s`) corner it is. -/
structure Vertex where
  hex : Hex
  corner : Corner
  deriving DecidableEq, Hashable, Repr, Ord, Inhabited

/-- The three canonical sides of a pointy-top hex. The other three sides
(south-west, west, north-west) are canonical sides of a neighbour. -/
inductive Side
  | ne
  | e
  | se
  deriving DecidableEq, Hashable, Repr, Ord, Inhabited

/-- An edge, named by the hex whose `ne`, `e` or `se` side it is. -/
structure Edge where
  hex : Hex
  side : Side
  deriving DecidableEq, Hashable, Repr, Ord, Inhabited

instance : LT Hex := ltOfOrd
instance : LE Hex := leOfOrd
instance : LT Vertex := ltOfOrd
instance : LE Vertex := leOfOrd
instance : LT Edge := ltOfOrd
instance : LE Edge := leOfOrd

namespace Hex

/-- The origin hex `⟨0, 0⟩`. -/
def origin : Hex := ⟨0, 0⟩

/-- Component-wise sum. -/
def add (a b : Hex) : Hex := ⟨a.q + b.q, a.r + b.r⟩

/-- Component-wise difference. -/
def sub (a b : Hex) : Hex := ⟨a.q - b.q, a.r - b.r⟩

instance : Add Hex := ⟨add⟩
instance : Sub Hex := ⟨sub⟩

/-- The implicit third cube coordinate, `s = -q - r`. -/
def s (h : Hex) : Int := -h.q - h.r

/-- Offset to the east neighbour. -/
def east (h : Hex) : Hex := ⟨h.q + 1, h.r⟩
/-- Offset to the north-east neighbour. -/
def northEast (h : Hex) : Hex := ⟨h.q + 1, h.r - 1⟩
/-- Offset to the north-west neighbour. -/
def northWest (h : Hex) : Hex := ⟨h.q, h.r - 1⟩
/-- Offset to the west neighbour. -/
def west (h : Hex) : Hex := ⟨h.q - 1, h.r⟩
/-- Offset to the south-west neighbour. -/
def southWest (h : Hex) : Hex := ⟨h.q - 1, h.r + 1⟩
/-- Offset to the south-east neighbour. -/
def southEast (h : Hex) : Hex := ⟨h.q, h.r + 1⟩

/-- The six neighbours, counter-clockwise from east:
`[E, NE, NW, W, SW, SE]`. -/
def neighbors (h : Hex) : List Hex :=
  [h.east, h.northEast, h.northWest, h.west, h.southWest, h.southEast]

/-- Hex distance: `max |Δq| |Δr| |Δs|`, which equals `(|Δq|+|Δr|+|Δs|)/2`. -/
def dist (a b : Hex) : Nat :=
  max (max (a.q - b.q).natAbs (a.r - b.r).natAbs) (a.q - b.q + (a.r - b.r)).natAbs

/-- `a` and `b` share a side. -/
def IsNeighbor (a b : Hex) : Prop := b ∈ a.neighbors

instance (a b : Hex) : Decidable (IsNeighbor a b) :=
  inferInstanceAs (Decidable (b ∈ a.neighbors))

/-- The six corners in canonical form, clockwise from the top:
`[N, NE, SE, S, SW, NW]`. -/
def vertices (h : Hex) : List Vertex :=
  [ ⟨h, .n⟩,
    ⟨h.northEast, .s⟩,
    ⟨h.southEast, .n⟩,
    ⟨h, .s⟩,
    ⟨h.southWest, .n⟩,
    ⟨h.northWest, .s⟩ ]

/-- The six sides in canonical form, clockwise from the north-east side:
`[NE, E, SE, SW, W, NW]`. -/
def edges (h : Hex) : List Edge :=
  [ ⟨h, .ne⟩,
    ⟨h, .e⟩,
    ⟨h, .se⟩,
    ⟨h.southWest, .ne⟩,
    ⟨h.west, .e⟩,
    ⟨h.northWest, .se⟩ ]

/-- Pixel centre of a hex for a pointy-top layout with circumradius `size`.
Screen `y` grows downwards. -/
def toPixel (h : Hex) (size : Float) : Float × Float :=
  let sqrt3 := Float.sqrt 3.0
  let q := Float.ofInt h.q
  let r := Float.ofInt h.r
  (size * (sqrt3 * q + sqrt3 / 2.0 * r), size * (1.5 * r))

end Hex

namespace Vertex

/-- The three hexes that share this vertex. The naming hex comes first. -/
def hexes : Vertex → List Hex
  | ⟨h, .n⟩ => [h, h.northWest, h.northEast]
  | ⟨h, .s⟩ => [h, h.southWest, h.southEast]

/-- The three edges that meet at this vertex. -/
def edges : Vertex → List Edge
  | ⟨h, .n⟩ => [⟨h, .ne⟩, ⟨h.northWest, .se⟩, ⟨h.northWest, .e⟩]
  | ⟨h, .s⟩ => [⟨h, .se⟩, ⟨h.southWest, .ne⟩, ⟨h.southWest, .e⟩]

/-- The three vertices joined to this one by an edge. The order matches
`Vertex.edges`. -/
def adjacentVertices : Vertex → List Vertex
  | ⟨h, .n⟩ => [⟨h.northEast, .s⟩, ⟨h.northWest, .s⟩, ⟨⟨h.q + 1, h.r - 2⟩, .s⟩]
  | ⟨h, .s⟩ => [⟨h.southEast, .n⟩, ⟨h.southWest, .n⟩, ⟨⟨h.q - 1, h.r + 2⟩, .n⟩]

/-- `v` and `w` are joined by an edge. -/
def IsAdjacent (v w : Vertex) : Prop := w ∈ v.adjacentVertices

instance (v w : Vertex) : Decidable (IsAdjacent v w) :=
  inferInstanceAs (Decidable (w ∈ v.adjacentVertices))

/-- Pixel position of a vertex for a pointy-top layout with circumradius `size`. -/
def toPixel (v : Vertex) (size : Float) : Float × Float :=
  let (x, y) := v.hex.toPixel size
  match v.corner with
  | .n => (x, y - size)
  | .s => (x, y + size)

end Vertex

namespace Edge

/-- The two endpoints of an edge. -/
def ends : Edge → Vertex × Vertex
  | ⟨h, .ne⟩ => (⟨h, .n⟩, ⟨h.northEast, .s⟩)
  | ⟨h, .e⟩ => (⟨h.northEast, .s⟩, ⟨h.southEast, .n⟩)
  | ⟨h, .se⟩ => (⟨h.southEast, .n⟩, ⟨h, .s⟩)

/-- The two hexes that share this edge. The naming hex comes first. -/
def hexes : Edge → List Hex
  | ⟨h, .ne⟩ => [h, h.northEast]
  | ⟨h, .e⟩ => [h, h.east]
  | ⟨h, .se⟩ => [h, h.southEast]

/-- `v` is an endpoint of `e`. -/
def HasEnd (e : Edge) (v : Vertex) : Prop := e.ends.1 = v ∨ e.ends.2 = v

instance (e : Edge) (v : Vertex) : Decidable (HasEnd e v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Two distinct edges that share an endpoint. -/
def IsAdjacent (e f : Edge) : Prop :=
  e ≠ f ∧ (f.HasEnd e.ends.1 ∨ f.HasEnd e.ends.2)

instance (e f : Edge) : Decidable (IsAdjacent e f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Pixel midpoint of an edge for a pointy-top layout with circumradius `size`. -/
def toPixel (e : Edge) (size : Float) : Float × Float :=
  let (x1, y1) := e.ends.1.toPixel size
  let (x2, y2) := e.ends.2.toPixel size
  ((x1 + x2) / 2.0, (y1 + y2) / 2.0)

end Edge

/-- Ring of hexes at distance exactly `k ≥ 1` from the origin, as six sides of
`k` hexes each, counter-clockwise from the east corner. `ring 0 = []`. -/
def ring (k : Nat) : List Hex :=
  let K : Int := k
  (List.range k).map (fun (j : Nat) => (⟨K, -(j : Int)⟩ : Hex)) ++
  (List.range k).map (fun (j : Nat) => (⟨K - j, -K⟩ : Hex)) ++
  (List.range k).map (fun (j : Nat) => (⟨-(j : Int), -K + j⟩ : Hex)) ++
  (List.range k).map (fun (j : Nat) => (⟨-K, j⟩ : Hex)) ++
  (List.range k).map (fun (j : Nat) => (⟨-K + j, K⟩ : Hex)) ++
  (List.range k).map (fun (j : Nat) => (⟨j, K - j⟩ : Hex))

/-- All hexes with distance at most `radius` from the origin: the origin,
then ring 1, ring 2, and so on. -/
def hexagon : Nat → List Hex
  | 0 => [Hex.origin]
  | k + 1 => hexagon k ++ ring (k + 1)

/-- Remove duplicates, keeping the first occurrence of each element. -/
def dedup {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- All canonical vertices touching a set of hexes, without duplicates, in
first-seen order. -/
def verticesOf (hs : List Hex) : List Vertex :=
  dedup (hs.flatMap Hex.vertices)

/-- All canonical edges touching a set of hexes, without duplicates, in
first-seen order. -/
def edgesOf (hs : List Hex) : List Edge :=
  dedup (hs.flatMap Hex.edges)

end HexGrid
