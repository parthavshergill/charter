import HexGrid.Basic

/-!
# HexGrid.Theorems

Structural guarantees, proved for all hexes (not only a finite board).
-/

namespace HexGrid

open Hex

/-! ## Neighbours -/

theorem neighbors_length (h : Hex) : h.neighbors.length = 6 := rfl

theorem neighbors_symm {a b : Hex} : b ∈ a.neighbors → a ∈ b.neighbors := by
  cases a; cases b
  simp [neighbors, east, northEast, northWest, west, southWest, southEast] <;> omega

theorem neighbors_nodup (h : Hex) : h.neighbors.Nodup := by
  cases h
  simp [neighbors, east, northEast, northWest, west, southWest, southEast] <;> omega

theorem not_mem_neighbors_self (h : Hex) : h ∉ h.neighbors := by
  cases h
  simp [neighbors, east, northEast, northWest, west, southWest, southEast] <;> omega

/-! ## Distance -/

theorem dist_symm (a b : Hex) : a.dist b = b.dist a := by
  simp [dist] <;> omega

theorem dist_self (a : Hex) : a.dist a = 0 := by
  simp [dist] <;> omega

theorem dist_eq_zero_iff {a b : Hex} : a.dist b = 0 ↔ a = b := by
  cases a; cases b
  simp [dist] <;> omega

private theorem natAbs_split (x y z : Int) (h : x = y + z) :
    x.natAbs ≤ y.natAbs + z.natAbs := h ▸ Int.natAbs_add_le y z

theorem dist_triangle (a b c : Hex) : a.dist c ≤ a.dist b + b.dist c := by
  have h1 := natAbs_split (a.q - c.q) (a.q - b.q) (b.q - c.q) (by omega)
  have h2 := natAbs_split (a.r - c.r) (a.r - b.r) (b.r - c.r) (by omega)
  have h3 := natAbs_split (a.q - c.q + (a.r - c.r)) (a.q - b.q + (a.r - b.r))
    (b.q - c.q + (b.r - c.r)) (by omega)
  simp only [dist]
  generalize (a.q - c.q).natAbs = x1 at *
  generalize (a.q - b.q).natAbs = x2 at *
  generalize (b.q - c.q).natAbs = x3 at *
  generalize (a.r - c.r).natAbs = y1 at *
  generalize (a.r - b.r).natAbs = y2 at *
  generalize (b.r - c.r).natAbs = y3 at *
  generalize (a.q - c.q + (a.r - c.r)).natAbs = z1 at *
  generalize (a.q - b.q + (a.r - b.r)).natAbs = z2 at *
  generalize (b.q - c.q + (b.r - c.r)).natAbs = z3 at *
  omega

theorem dist_eq_one_iff_mem_neighbors {a b : Hex} : a.dist b = 1 ↔ b ∈ a.neighbors := by
  cases a; cases b
  simp [dist, neighbors, east, northEast, northWest, west, southWest, southEast] <;> omega

/-! ## Vertices -/

theorem vertex_hexes_length (v : Vertex) : v.hexes.length = 3 := by
  rcases v with ⟨h, c⟩; cases c <;> rfl

theorem vertex_hexes_nodup (v : Vertex) : v.hexes.Nodup := by
  rcases v with ⟨⟨q, r⟩, c⟩
  cases c <;>
  simp [Vertex.hexes, northWest, northEast, southWest, southEast] <;> omega

theorem vertices_length (h : Hex) : h.vertices.length = 6 := rfl

theorem vertices_nodup (h : Hex) : h.vertices.Nodup := by
  rcases h with ⟨q, r⟩
  simp [vertices, northEast, southEast, southWest, northWest] <;> omega

/-- Canonical forms agree: `v` is a corner of `h` exactly when `h` is one of
the three hexes of `v`. -/
theorem mem_vertices_iff_mem_hexes {h : Hex} {v : Vertex} : v ∈ h.vertices ↔ h ∈ v.hexes := by
  rcases h with ⟨q, r⟩; rcases v with ⟨⟨q', r'⟩, c⟩
  cases c <;>
  simp [vertices, Vertex.hexes, northEast, southEast, southWest, northWest] <;> omega

theorem vertex_edges_length (v : Vertex) : v.edges.length = 3 := by
  rcases v with ⟨h, c⟩; cases c <;> rfl

theorem vertex_edges_nodup (v : Vertex) : v.edges.Nodup := by
  rcases v with ⟨⟨q, r⟩, c⟩
  cases c <;>
  simp [Vertex.edges, northWest, southWest] <;> omega

/-- The edges at a vertex are exactly the edges having it as an endpoint. -/
theorem mem_vertex_edges_iff {v : Vertex} {e : Edge} : e ∈ v.edges ↔ e.HasEnd v := by
  rcases v with ⟨⟨q, r⟩, c⟩; rcases e with ⟨⟨q', r'⟩, d⟩
  cases c <;> cases d <;>
  simp [Vertex.edges, Edge.HasEnd, Edge.ends, northWest, southWest, northEast, southEast] <;> omega

theorem adjacentVertices_length (v : Vertex) : v.adjacentVertices.length = 3 := by
  rcases v with ⟨h, c⟩; cases c <;> rfl

theorem adjacentVertices_nodup (v : Vertex) : v.adjacentVertices.Nodup := by
  rcases v with ⟨⟨q, r⟩, c⟩
  cases c <;>
  simp [Vertex.adjacentVertices, northWest, southWest, northEast, southEast] <;> omega

/-- Vertex adjacency is symmetric. -/
theorem adjacent_symm {v w : Vertex} : w ∈ v.adjacentVertices → v ∈ w.adjacentVertices := by
  rcases v with ⟨⟨q, r⟩, c⟩; rcases w with ⟨⟨q', r'⟩, d⟩
  cases c <;> cases d <;>
  simp [Vertex.adjacentVertices, northWest, southWest, northEast, southEast] <;> omega

theorem not_adjacent_self (v : Vertex) : v ∉ v.adjacentVertices := by
  rcases v with ⟨⟨q, r⟩, c⟩
  cases c <;>
  simp [Vertex.adjacentVertices, northWest, southWest, northEast, southEast] <;> omega

/-- Two vertices are adjacent exactly when some edge joins them. -/
theorem mem_adjacentVertices_iff {v w : Vertex} :
    w ∈ v.adjacentVertices ↔ ∃ e : Edge, e.ends = (v, w) ∨ e.ends = (w, v) := by
  constructor
  · rcases v with ⟨⟨q, r⟩, c⟩
    cases c <;>
    simp [Vertex.adjacentVertices, northWest, southWest, northEast, southEast] <;>
    rintro (rfl | rfl | rfl)
    · exact ⟨⟨⟨q, r⟩, .ne⟩, by simp [Edge.ends, northEast]⟩
    · exact ⟨⟨⟨q, r - 1⟩, .se⟩, by simp [Edge.ends, southEast]⟩
    · exact ⟨⟨⟨q, r - 1⟩, .e⟩, by simp [Edge.ends, northEast, southEast] <;> omega⟩
    · exact ⟨⟨⟨q, r⟩, .se⟩, by simp [Edge.ends, southEast]⟩
    · exact ⟨⟨⟨q - 1, r + 1⟩, .ne⟩, by simp [Edge.ends, northEast] <;> omega⟩
    · exact ⟨⟨⟨q - 1, r + 1⟩, .e⟩, by simp [Edge.ends, northEast, southEast] <;> omega⟩
  · rintro ⟨⟨⟨q, r⟩, d⟩, he | he⟩ <;> cases d <;>
    simp [Edge.ends, northEast, southEast] at he <;>
    obtain ⟨rfl, rfl⟩ := he <;>
    simp [Vertex.adjacentVertices, northWest, southWest, northEast, southEast] <;> omega

/-! ## Edges -/

theorem edges_length (h : Hex) : h.edges.length = 6 := rfl

theorem edges_nodup (h : Hex) : h.edges.Nodup := by
  rcases h with ⟨q, r⟩
  simp [edges, southWest, west, northWest] <;> omega

theorem edge_hexes_length (e : Edge) : e.hexes.length = 2 := by
  rcases e with ⟨h, d⟩; cases d <;> rfl

theorem edge_hexes_nodup (e : Edge) : e.hexes.Nodup := by
  rcases e with ⟨⟨q, r⟩, d⟩
  cases d <;>
  simp [Edge.hexes, northEast, east, southEast] <;> omega

/-- Canonical forms agree: `e` is a side of `h` exactly when `h` is one of the
two hexes of `e`. -/
theorem mem_edges_iff_mem_hexes {h : Hex} {e : Edge} : e ∈ h.edges ↔ h ∈ e.hexes := by
  rcases h with ⟨q, r⟩; rcases e with ⟨⟨q', r'⟩, d⟩
  cases d <;>
  simp [edges, Edge.hexes, southWest, west, northWest, northEast, east, southEast] <;> omega

/-- The two ends of an edge are different vertices. -/
theorem edge_ends_ne (e : Edge) : e.ends.1 ≠ e.ends.2 := by
  rcases e with ⟨⟨q, r⟩, d⟩
  cases d <;> simp [Edge.ends, northEast, southEast]

/-- An edge's hexes are exactly the hexes shared by both of its ends. -/
theorem mem_edge_hexes_iff {e : Edge} {h : Hex} :
    h ∈ e.hexes ↔ h ∈ e.ends.1.hexes ∧ h ∈ e.ends.2.hexes := by
  rcases e with ⟨⟨q, r⟩, d⟩; rcases h with ⟨q', r'⟩
  cases d <;>
  simp [Edge.hexes, Edge.ends, Vertex.hexes, northEast, east, southEast, northWest, southWest] <;> omega

/-- The two hexes of an edge are neighbours. -/
theorem edge_hexes_neighbors (e : Edge) :
    ∃ a b, e.hexes = [a, b] ∧ b ∈ a.neighbors := by
  rcases e with ⟨h, d⟩
  cases d <;> exact ⟨_, _, rfl, by simp [neighbors]⟩

/-- Every edge's ends are corners of each of its hexes. -/
theorem edge_ends_mem_vertices {e : Edge} {h : Hex} (he : h ∈ e.hexes) :
    e.ends.1 ∈ h.vertices ∧ e.ends.2 ∈ h.vertices := by
  rw [mem_vertices_iff_mem_hexes, mem_vertices_iff_mem_hexes]
  exact mem_edge_hexes_iff.mp he

/-! ## Hexagonal boards -/

theorem ring_length (k : Nat) : (ring k).length = 6 * k := by
  simp [ring] <;> omega

/-- A hexagonal board of radius `r` has `3r² + 3r + 1` hexes. -/
theorem hexagon_length (r : Nat) : (hexagon r).length = 3 * r * r + 3 * r + 1 := by
  induction r with
  | zero => rfl
  | succ k ih =>
    simp [hexagon, ih, ring_length]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

theorem mem_ring_iff {k : Nat} {h : Hex} (hk : 0 < k) : h ∈ ring k ↔ h.dist origin = k := by
  rcases h with ⟨q, r⟩
  simp only [ring, List.mem_append, List.mem_map, List.mem_range, Hex.mk.injEq, dist, origin]
  constructor
  · rintro (((((⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩) | ⟨j, hj, h1, h2⟩) | ⟨j, hj, h1, h2⟩) |
      ⟨j, hj, h1, h2⟩) | ⟨j, hj, h1, h2⟩) <;> omega
  · intro hd
    by_cases c0 : q = k ∧ r > -k
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(-r).toNat, by omega, by omega, by omega⟩))))
    by_cases c1 : r = -k ∧ q > 0
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(k - q).toNat, by omega, by omega, by omega⟩))))
    by_cases c2 : q + r = -k ∧ q ≤ 0 ∧ q > -k
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(-q).toNat, by omega, by omega, by omega⟩)))
    by_cases c3 : q = -k ∧ r ≥ 0 ∧ r < k
    · exact Or.inl (Or.inl (Or.inr ⟨r.toNat, by omega, by omega, by omega⟩))
    by_cases c4 : r = k ∧ q < 0
    · exact Or.inl (Or.inr ⟨(q + k).toNat, by omega, by omega, by omega⟩)
    · exact Or.inr ⟨q.toNat, by omega, by omega, by omega⟩

/-- `hexagon r` contains exactly the hexes within distance `r` of the origin. -/
theorem mem_hexagon_iff {r : Nat} {h : Hex} : h ∈ hexagon r ↔ h.dist origin ≤ r := by
  induction r with
  | zero =>
    simp [hexagon]
    rw [dist_eq_zero_iff]
  | succ k ih =>
    simp [hexagon, ih, mem_ring_iff (Nat.succ_pos k)]
    omega

theorem ring_nodup (k : Nat) : (ring k).Nodup := by
  simp only [ring, List.nodup_append, List.mem_append, List.mem_map, List.mem_range]
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  case refine_1 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_2 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_4 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_6 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_8 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_10 =>
    exact List.Pairwise.map _ (fun a b hab h => by simp only [Hex.mk.injEq] at h; omega)
      List.nodup_range
  case refine_3 =>
    rintro a ha b ⟨j, hj, rfl⟩ rfl
    try simp only [or_assoc] at ha
    rcases ha with ⟨i, hi, h⟩ <;> simp only [Hex.mk.injEq] at h <;> omega
  case refine_5 =>
    rintro a ha b ⟨j, hj, rfl⟩ rfl
    try simp only [or_assoc] at ha
    rcases ha with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> simp only [Hex.mk.injEq] at h <;> omega
  case refine_7 =>
    rintro a ha b ⟨j, hj, rfl⟩ rfl
    try simp only [or_assoc] at ha
    rcases ha with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> simp only [Hex.mk.injEq] at h <;> omega
  case refine_9 =>
    rintro a ha b ⟨j, hj, rfl⟩ rfl
    try simp only [or_assoc] at ha
    rcases ha with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> simp only [Hex.mk.injEq] at h <;> omega
  case refine_11 =>
    rintro a ha b ⟨j, hj, rfl⟩ rfl
    try simp only [or_assoc] at ha
    rcases ha with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> simp only [Hex.mk.injEq] at h <;> omega

/-- A hexagonal board lists each hex once. -/
theorem hexagon_nodup (r : Nat) : (hexagon r).Nodup := by
  induction r with
  | zero => simp [hexagon]
  | succ k ih =>
    simp only [hexagon, List.nodup_append]
    refine ⟨ih, ring_nodup _, fun a ha b hb hab => ?_⟩
    subst hab
    rw [mem_hexagon_iff] at ha
    rw [mem_ring_iff (Nat.succ_pos k)] at hb
    omega

/-! ## Vertex and edge sets of a board -/

private theorem mem_dedup_go {α : Type} [DecidableEq α] (l acc : List α) (x : α) :
    x ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rename_i hy
      have : y ∈ acc := by simpa using hy
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl this
        · exact Or.inr h
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

private theorem nodup_dedup_go {α : Type} [DecidableEq α] (l acc : List α) (hacc : acc.Nodup) :
    (l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons y l ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact hacc
    · rename_i hy
      have : y ∉ acc := by simpa using hy
      rw [List.nodup_append]
      refine ⟨hacc, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb hab
      exact this ha

theorem mem_dedup {α : Type} [DecidableEq α] {l : List α} {x : α} : x ∈ dedup l ↔ x ∈ l := by
  simp only [dedup]; rw [mem_dedup_go]; simp

theorem dedup_nodup {α : Type} [DecidableEq α] (l : List α) : (dedup l).Nodup :=
  nodup_dedup_go l [] List.nodup_nil

/-- The vertices of a board are exactly the corners of its hexes. -/
theorem mem_verticesOf {hs : List Hex} {v : Vertex} :
    v ∈ verticesOf hs ↔ ∃ h ∈ hs, h ∈ v.hexes := by
  simp only [verticesOf, mem_dedup, List.mem_flatMap, mem_vertices_iff_mem_hexes]

theorem verticesOf_nodup (hs : List Hex) : (verticesOf hs).Nodup := dedup_nodup _

/-- The edges of a board are exactly the sides of its hexes. -/
theorem mem_edgesOf {hs : List Hex} {e : Edge} :
    e ∈ edgesOf hs ↔ ∃ h ∈ hs, h ∈ e.hexes := by
  simp only [edgesOf, mem_dedup, List.mem_flatMap, mem_edges_iff_mem_hexes]

theorem edgesOf_nodup (hs : List Hex) : (edgesOf hs).Nodup := dedup_nodup _

end HexGrid
