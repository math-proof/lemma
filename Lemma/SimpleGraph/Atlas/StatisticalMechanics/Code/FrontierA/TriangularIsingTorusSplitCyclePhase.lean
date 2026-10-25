import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitCyclePhase
open StatMech StatMech.FrontierA


/--
[triangularTorusSplitEmbed_phaseProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitCyclePhase.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_phaseProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle) :
-- imply
  let q := triangularTorusSplitEmbedWalk L p letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ letI : NeZero q.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr (triangularTorusSplitEmbedWalk_isCycle L p hp).not_nil))⟩ kwLoopPhaseProduct (triangularTorusGraphPhase (3 * L) rho 1 1) (kwGraphCycleDartLoop q) = kwLoopPhaseProduct (kwPhaseGauge (triangularTorusSplitPhaseGauge L rho) (kwLocalAngularSplitPhase (triangularTorusLocalAngularData L rho hrho))) (kwGraphCycleDartLoop p) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_phaseProduct L rho hrho p hp

/--
[triangularTorus_localAngularSplit_shiftedCyclePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitCyclePhase.lean)
-/
@[path]
private lemma triangularTorus_localAngularSplit_shiftedCyclePhase_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  KWLocalAngularSplitShiftedCyclePhase (triangularTorusLocalAngularData L rho hrho) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) (triangularTorusSurfaceSpin 0 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_localAngularSplit_shiftedCyclePhase L rho hrho


-- created on 2026-10-23
