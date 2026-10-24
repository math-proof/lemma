import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexPlanePeriod_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlanePeriod_re_eq
  {z : Site 2} :
-- imply
  (triHexPlanePeriod z).re = z 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanePeriod_re z

/--
[triHexPlanePeriod_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlanePeriod_im_eq
  {z : Site 2} :
-- imply
  (triHexPlanePeriod z).im = z 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanePeriod_im z

/--
[triHexPlanePeriod_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlanePeriod_injective_eq :
-- imply
  Function.Injective triHexPlanePeriod := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanePeriod_injective

/--
[triHexPlaneCoordinates_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlaneCoordinates_apply_zero_eq
  {z : Complex} :
-- imply
  triHexPlaneCoordinates z 0 = z.re := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlaneCoordinates_apply_zero z

/--
[triHexPlaneCoordinates_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlaneCoordinates_apply_one_eq
  {z : Complex} :
-- imply
  triHexPlaneCoordinates z 1 = z.im := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlaneCoordinates_apply_one z

/--
[triHexPlaneCoordinates_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlaneCoordinates_period_eq
  {z : Site 2}
  {i : Fin 2} :
-- imply
  triHexPlaneCoordinates (triHexPlanePeriod z) i = z i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlaneCoordinates_period z i

/--
[triangularPlaneVertex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularPlaneVertex_apply_eq
  {z : Site 2} :
-- imply
  triangularPlaneVertex z = triHexPlanePeriod z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPlaneVertex_apply z

/--
[triangularPlaneVertex_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularPlaneVertex_shift_eq
  {z x : Site 2} :
-- imply
  triangularPlaneVertex (triangular.shift z x) = triangularPlaneVertex x + triHexPlanePeriod z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPlaneVertex_shift z x

/--
[triHexPlanePeriod_bounded_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triHexPlanePeriod_bounded_finite_eq
  {R : Real} :
-- imply
  {z : Site 2 | ‖triHexPlanePeriod z‖ <= R}.Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanePeriod_bounded_finite R

/--
[triangularPlaneVertex_bounded_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularPlaneVertex_bounded_finite_eq
  {R : Real} :
-- imply
  {z : Site 2 | ‖(triangularPlaneVertex z : Complex)‖ <= R}.Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPlaneVertex_bounded_finite R

/--
[triangularStraightEdgeArc_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_injective_eq
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  Function.Injective (triangularStraightEdgeArc hxy) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_injective hxy

/--
[triangularStraightEdgeArc_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_symm_eq
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  Set.range (triangularStraightEdgeArc hxy.symm) = Set.range (triangularStraightEdgeArc hxy) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_symm hxy

/--
[triangularStraightEdgeArc_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_shift_eq
  {z : Site 2}
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  Set.range (triangularStraightEdgeArc ((triangular.shift_adj z x y).2 hxy)) = (fun p => p + triHexPlanePeriod z) '' Set.range (triangularStraightEdgeArc hxy) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_shift z hxy

/--
[triangularStraightEdge_length_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularStraightEdge_length_le_two_eq
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  dist (triangularPlaneVertex x) (triangularPlaneVertex y) <= 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdge_length_le_two hxy

/--
[hexagonalFaceCenterOffset_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalFaceCenterOffset_false_eq :
-- imply
  hexagonalFaceCenterOffset false = (1 / 3 : Real) + (1 / 3 : Real) * Complex.I := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFaceCenterOffset_false

/--
[hexagonalFaceCenterOffset_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalFaceCenterOffset_true_eq :
-- imply
  hexagonalFaceCenterOffset true = -(1 / 3 : Real) - (1 / 3 : Real) * Complex.I := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFaceCenterOffset_true

/--
[hexagonalFaceCenterOffset_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalFaceCenterOffset_norm_le_one_eq
  {white : Bool} :
-- imply
  ‖hexagonalFaceCenterOffset white‖ <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFaceCenterOffset_norm_le_one white

/--
[hexagonalPlaneVertexValue_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalPlaneVertexValue_injective_eq :
-- imply
  Function.Injective hexagonalPlaneVertexValue := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertexValue_injective

/--
[hexagonalPlaneVertex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalPlaneVertex_apply_eq
  {u : HexVertex} :
-- imply
  hexagonalPlaneVertex u = hexagonalPlaneVertexValue u := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertex_apply u

/--
[hexagonalPlaneVertex_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalPlaneVertex_shift_eq
  {z : Site 2}
  {u : HexVertex} :
-- imply
  hexagonalPlaneVertex (hexagonal.shift z u) = hexagonalPlaneVertex u + triHexPlanePeriod z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertex_shift z u

/--
[hexagonalPlaneVertex_bounded_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalPlaneVertex_bounded_finite_eq
  {R : Real} :
-- imply
  {u : HexVertex | ‖(hexagonalPlaneVertex u : Complex)‖ <= R}.Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertex_bounded_finite R

/--
[hexagonalStraightEdgeArc_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_injective_eq
  {u v : HexVertex}
-- given
  (huv : hexagonalGraph.Adj u v) :
-- imply
  Function.Injective (hexagonalStraightEdgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_injective huv

/--
[hexagonalStraightEdgeArc_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_symm_eq
  {u v : HexVertex}
-- given
  (huv : hexagonalGraph.Adj u v) :
-- imply
  Set.range (hexagonalStraightEdgeArc huv.symm) = Set.range (hexagonalStraightEdgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_symm huv

/--
[hexagonalStraightEdgeArc_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_shift_eq
  {z : Site 2}
  {u v : HexVertex}
-- given
  (huv : hexagonalGraph.Adj u v) :
-- imply
  Set.range (hexagonalStraightEdgeArc ((hexagonal.shift_adj z u v).2 huv)) = (fun p => p + triHexPlanePeriod z) '' Set.range (hexagonalStraightEdgeArc huv) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_shift z huv

/--
[hexagonalStraightEdge_length_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdge_length_le_two_eq
  {u v : HexVertex}
-- given
  (huv : hexagonalGraph.Adj u v) :
-- imply
  dist (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) <= 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdge_length_le_two huv

/--
[triangularStraightEdgeArc_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_locallyFinite_eq
  {K : Set Complex}
-- given
  (hK : IsCompact K) :
-- imply
  {xy : Site 2 × Site 2 | ∃ hxy : triangularGraph.Adj xy.1 xy.2, (Set.range (triangularStraightEdgeArc hxy) ∩ K).Nonempty}.Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_locallyFinite K hK

/--
[hexagonalStraightEdgeArc_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_locallyFinite_eq
  {K : Set Complex}
-- given
  (hK : IsCompact K) :
-- imply
  {uv : HexVertex × HexVertex | ∃ huv : hexagonalGraph.Adj uv.1 uv.2, (Set.range (hexagonalStraightEdgeArc huv) ∩ K).Nonempty}.Finite := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_locallyFinite K hK


-- created on 2026-10-23
