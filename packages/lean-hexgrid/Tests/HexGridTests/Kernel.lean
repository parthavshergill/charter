import HexGrid
/-! Kernel-checked (`decide`, no `native_decide`) facts about concrete boards. -/
open HexGrid

namespace HexGridTests.Kernel

set_option maxRecDepth 20000

theorem board2_hexes : (hexagon 2).length = 19 := by decide
theorem board2_vertices : (verticesOf (hexagon 2)).length = 54 := by decide
theorem board2_edges : (edgesOf (hexagon 2)).length = 72 := by decide
theorem board3_vertices : (verticesOf (hexagon 3)).length = 96 := by decide
theorem board3_edges : (edgesOf (hexagon 3)).length = 132 := by decide
/-- Every vertex of the radius-2 board touches 3 hexes, all inside radius 3. -/
theorem board2_vertex_hexes_in_r3 :
    (verticesOf (hexagon 2)).all (fun v => v.hexes.all fun h => (hexagon 3).contains h) = true := by
  decide

end HexGridTests.Kernel
