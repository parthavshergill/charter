import HexGrid
/-! Axiom audit for every theorem listed under README "Guarantees".
Expected: only `propext`, `Quot.sound`, `Classical.choice` (or none). -/
open HexGrid

#print axioms neighbors_symm
#print axioms neighbors_nodup
#print axioms not_mem_neighbors_self
#print axioms dist_symm
#print axioms dist_self
#print axioms dist_eq_zero_iff
#print axioms dist_triangle
#print axioms dist_eq_one_iff_mem_neighbors
#print axioms vertex_hexes_length
#print axioms vertex_hexes_nodup
#print axioms vertices_nodup
#print axioms mem_vertices_iff_mem_hexes
#print axioms vertex_edges_nodup
#print axioms mem_vertex_edges_iff
#print axioms adjacentVertices_nodup
#print axioms adjacent_symm
#print axioms not_adjacent_self
#print axioms mem_adjacentVertices_iff
#print axioms edges_nodup
#print axioms edge_hexes_length
#print axioms mem_edges_iff_mem_hexes
#print axioms edge_ends_ne
#print axioms mem_edge_hexes_iff
#print axioms edge_hexes_neighbors
#print axioms edge_ends_mem_vertices
#print axioms hexagon_length
#print axioms mem_hexagon_iff
#print axioms hexagon_nodup
#print axioms mem_verticesOf
#print axioms verticesOf_nodup
#print axioms mem_edgesOf
#print axioms edgesOf_nodup
