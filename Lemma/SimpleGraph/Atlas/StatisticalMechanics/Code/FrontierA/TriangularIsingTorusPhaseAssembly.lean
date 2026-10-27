import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhaseAssembly
open StatMech StatMech.FrontierA


/--
[triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhaseAssembly.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hprimitive : TriangularTorusZeroHomologyWinding L)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = -(surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset)) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign L rho hrho hprimitive p hp


-- created on 2026-10-23
