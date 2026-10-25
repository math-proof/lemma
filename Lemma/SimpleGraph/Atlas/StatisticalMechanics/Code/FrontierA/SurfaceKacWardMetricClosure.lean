import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part3
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas


/--
[developed_phase_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma developed_phase_product_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) = (surfaceParitySign (atlas.developedTurningParity p) : Complex) := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.developed_phase_product atlas p hp

/--
[developedConeDefect_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma developedConeDefect_even_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root} :
-- imply
  exists k : Int, (∑ cone ∈ atlas.developedConeSupport p, (atlas.coneOrder cone - 1)) = 2 * k := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.developedConeDefect_even atlas p

/--
[admissibleConeAngles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma admissibleConeAngles_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  atlas.developedTurningParity p = 1 + surfaceBaseQuadraticParity (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset) := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.admissibleConeAngles atlas p hp

/--
[toClosedFlatSurfaceGraphAtlas_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma toClosedFlatSurfaceGraphAtlas_admissible_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G} :
-- imply
  atlas.toClosedFlatSurfaceGraphAtlas.AdmissibleConeAngles := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.toClosedFlatSurfaceGraphAtlas_admissible atlas

/--
[simple_cycle_holonomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma simple_cycle_holonomy_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) = -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.simple_cycle_holonomy atlas p hp

/--
[kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean)
-/
@[path]
private lemma kacWard_arf_formula_eq
  {g : Nat}
  {Cone : Type v}
  [Fintype Cone]
  [DecidableEq Cone]
  {atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G}
-- given
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G atlas.phase atlas.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G atlas.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.ClosedMetricFlatSurfaceGraphAtlas.kacWard_arf_formula atlas weight


-- created on 2026-10-23
