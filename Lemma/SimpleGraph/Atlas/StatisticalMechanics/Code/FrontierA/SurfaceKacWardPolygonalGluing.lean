import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing.Part4
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.ClosedPolygonalGluingFlatSurfaceEmbedding


/--
[surfaceWalkPrefixHomology_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma surfaceWalkPrefixHomology_zero_eq
  {g : Nat}
  {V : Type u}
  {G : SimpleGraph V}
  {root : V}
  {p : G.Walk root root}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g) :
-- imply
  surfaceWalkPrefixHomology edgeClass p 0 = 0 := by
-- proof
  apply StatMech.FrontierA.surfaceWalkPrefixHomology_zero edgeClass p

/--
[surfaceWalkPrefixHomology_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma surfaceWalkPrefixHomology_length_eq
  {g : Nat}
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {root : V}
  {p : G.Walk root root}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hp : p.IsCycle) :
-- imply
  surfaceWalkPrefixHomology edgeClass p p.darts.length = surfaceSubgraphHomology edgeClass p.edges.toFinset := by
-- proof
  apply StatMech.FrontierA.surfaceWalkPrefixHomology_length edgeClass p hp

/--
[sum_surfaceWalkQuadraticIncrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma sum_surfaceWalkQuadraticIncrement_eq
  {g : Nat}
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {root : V}
  {p : G.Walk root root}
-- given
  (edgeClass : Sym2 V -> SurfaceHomology g)
  (hp : p.IsCycle) :
-- imply
  (∑ k : Fin p.darts.length, surfaceWalkQuadraticIncrement edgeClass p k) = (surfaceBaseQuadraticParity (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val := by
-- proof
  apply StatMech.FrontierA.sum_surfaceWalkQuadraticIncrement edgeClass p hp

/--
[developedTurnLift_constructed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma developedTurnLift_constructed_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k : Fin p.darts.length, (embedding.angle (kwGraphCycleDartLoop p (k + 1)) - embedding.angle (kwGraphCycleDartLoop p k)).toReal = (((Complex.arg ((embedding.developedPolygon p hp).edgeVector (k + 1)) : Real.Angle) - (Complex.arg ((embedding.developedPolygon p hp).edgeVector k) : Real.Angle)).toReal) + (embedding.chartTransitionIndex p k : Real) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalGluingFlatSurfaceEmbedding.developedTurnLift_constructed embedding p hp

/--
[chartIndexGaussBonnet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma chartIndexGaussBonnet_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, embedding.chartTransitionIndex p k) = (surfaceBaseQuadraticParity (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val + 2 * embedding.chartRegularTurnCorrection p + ∑ cone ∈ embedding.developedConeSupport p, (embedding.coneOrder cone - 1) := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalGluingFlatSurfaceEmbedding.chartIndexGaussBonnet embedding p hp

/--
[developedGaussBonnet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma developedGaussBonnet_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  kwClosedWalkAngleRotationNumber embedding.angle p = 1 + (surfaceBaseQuadraticParity (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val + 2 * (embedding.toClosedPolygonalFlatSurfaceGraphAtlas.developedPolygonHalf p + embedding.chartRegularTurnCorrection p) + ∑ cone ∈ embedding.developedConeSupport p, (embedding.coneOrder cone - 1) := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalGluingFlatSurfaceEmbedding.developedGaussBonnet embedding p hp

/--
[kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean)
-/
@[path]
private lemma kacWard_arf_formula_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G (ClosedMetricFlatSurfaceGraphAtlas.phase (ClosedPolygonalFlatSurfaceGraphAtlas.toClosedMetricFlatSurfaceGraphAtlas embedding.toClosedPolygonalFlatSurfaceGraphAtlas)) embedding.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G embedding.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G embedding.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G embedding.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.ClosedPolygonalGluingFlatSurfaceEmbedding.kacWard_arf_formula embedding weight


-- created on 2026-10-23
