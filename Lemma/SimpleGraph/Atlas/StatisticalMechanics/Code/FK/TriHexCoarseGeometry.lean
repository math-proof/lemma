import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangularGraph_connected_eq :
-- imply
  triangularGraph.Connected := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularGraph_connected

/--
[triangular_adj_sub_mem_box_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangular_adj_sub_mem_box_one_eq
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  y - x ∈ box 2 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_adj_sub_mem_box_one hxy

/--
[triangular_walk_sub_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangular_walk_sub_mem_box_eq
  {x y : Site 2}
  {w : triangularGraph.Walk x y} :
-- imply
  y - x ∈ box 2 w.length := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_walk_sub_mem_box w

/--
[triangular_sub_mem_box_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangular_sub_mem_box_dist_eq
  {x y : Site 2} :
-- imply
  y - x ∈ box 2 (triangularGraph.dist x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_sub_mem_box_dist x y

/--
[triangular_dist_le_coordinate_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangular_dist_le_coordinate_sum_eq
  {x y : Site 2} :
-- imply
  triangularGraph.dist x y ≤ (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_dist_le_coordinate_sum x y

/--
[triangular_dist_le_two_mul_of_sub_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma triangular_dist_le_two_mul_of_sub_mem_box_eq
  {x y : Site 2}
  {n : Nat}
-- given
  (hxy : y - x ∈ box 2 n) :
-- imply
  triangularGraph.dist x y ≤ 2 * n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_dist_le_two_mul_of_sub_mem_box hxy

/--
[hexagonalGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma hexagonalGraph_connected_eq :
-- imply
  hexagonalGraph.Connected := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalGraph_connected

/--
[hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two_eq
  {u v : HexVertex} :
-- imply
  hexagonalGraph.dist u v ≤ 2 * triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) + 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two u v

/--
[half_hexagonal_dist_le_triangular_anchor_dist_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma half_hexagonal_dist_le_triangular_anchor_dist_add_one_eq
  {u v : HexVertex} :
-- imply
  (1 / 2 : Real) * (hexagonalGraph.dist u v : Real) ≤ (triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) : Real) + 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.half_hexagonal_dist_le_triangular_anchor_dist_add_one u v

/--
[hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean)
-/
@[path]
private lemma hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box_eq
  {u v : HexVertex}
  {n : Nat}
-- given
  (huv : hexToTriAnchor v - hexToTriAnchor u ∈ box 2 n) :
-- imply
  hexagonalGraph.dist u v ≤ 4 * n + 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box huv


-- created on 2026-10-23
