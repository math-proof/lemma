import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[ClosedFlatSurfaceGraphAtlas.phase_sq_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean)
-/
@[path]
private lemma phase_sq_transport_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {atlas : ClosedFlatSurfaceGraphAtlas g G}
  {dart next : G.Dart}
-- given
  (hadj : G.DartAdj dart next)
  (hne : dart.edge ≠ next.edge) :
-- imply
  atlas.phase dart next ^ 2 * atlas.direction dart = atlas.direction next := by
-- proof
  apply StatMech.FrontierA.ClosedFlatSurfaceGraphAtlas.phase_sq_transport atlas dart next hadj hne

/--
[surfaceParitySign_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean)
-/
@[path]
private lemma surfaceParitySign_one_add_eq
  {z : Fin 2} :
-- imply
  (surfaceParitySign (1 + z) : Complex) = -(surfaceParitySign z : Complex) := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_one_add z

/--
[ClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean)
-/
@[path]
private lemma simple_cycle_holonomy_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {atlas : ClosedFlatSurfaceGraphAtlas g G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hadmissible : atlas.AdmissibleConeAngles)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) = -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
-- proof
  apply StatMech.FrontierA.ClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy atlas hadmissible p hp

/--
[closedFlatSurfaceAtlas_kacWard_arf_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean)
-/
@[path]
private lemma closedFlatSurfaceAtlas_kacWard_arf_formula_eq
  {g : Nat}
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {atlas : ClosedFlatSurfaceGraphAtlas g G}
-- given
  (hadmissible : atlas.AdmissibleConeAngles)
  (weight : Sym2 V -> Real) :
-- imply
  (forall lambda : SurfaceSpinStructure g, (1 - surfaceTwistedKacWardMatrix G atlas.phase atlas.edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda : Complex)) /\ surfaceUnsignedSectorSum (surfaceGraphSectorWeight G atlas.edgeClass weight) = ((2 : Real) ^ g)⁻¹ * ∑ lambda : SurfaceSpinStructure g, surfaceParitySign (surfaceArfParity lambda) * surfaceTwistedSectorRoot (surfaceGraphSectorWeight G atlas.edgeClass weight) lambda := by
-- proof
  apply StatMech.FrontierA.closedFlatSurfaceAtlas_kacWard_arf_formula G atlas hadmissible weight


-- created on 2026-10-23
