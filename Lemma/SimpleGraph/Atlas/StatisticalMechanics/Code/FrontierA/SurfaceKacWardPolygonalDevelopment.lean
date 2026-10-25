import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.ClosedPolygonalFlatSurfaceGraphAtlas


/--
[exists_developedPolygon_odd_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean)
-/
@[path]
private lemma exists_developedPolygon_odd_winding_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ ∃ winding : Int, (∑ k : Fin p.darts.length, ((Complex.arg ((atlas.developedPolygon p hp).edgeVector (k + 1)) : Real.Angle) - (Complex.arg ((atlas.developedPolygon p hp).edgeVector k) : Real.Angle)).toReal : Real) = (winding : Real) * (2 * Real.pi) ∧ Odd winding := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalFlatSurfaceGraphAtlas.exists_developedPolygon_odd_winding atlas p hp

/--
[developedPolygon_winding_eq_two_mul_half_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean)
-/
@[path]
private lemma developedPolygon_winding_eq_two_mul_half_add_one_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ let winding := Classical.choose (atlas.exists_developedPolygon_odd_winding p hp) winding = 2 * atlas.developedPolygonHalf p + 1 := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalFlatSurfaceGraphAtlas.developedPolygon_winding_eq_two_mul_half_add_one atlas p hp

/--
[developedGaussBonnet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean)
-/
@[path]
private lemma developedGaussBonnet_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  kwClosedWalkAngleRotationNumber atlas.angle p = 1 + (surfaceBaseQuadraticParity (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)).val + 2 * (atlas.developedPolygonHalf p + atlas.chartRegularTurnCorrection p) + ∑ cone ∈ atlas.developedConeSupport p, (atlas.coneOrder cone - 1) := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalFlatSurfaceGraphAtlas.developedGaussBonnet atlas p hp

/--
[kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalDevelopment.lean)
-/
@[path]
private lemma kacWard_arf_formula_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G atlas.toClosedMetricFlatSurfaceGraphAtlas.phase atlas.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G atlas.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalFlatSurfaceGraphAtlas.kacWard_arf_formula atlas weight


-- created on 2026-10-23
