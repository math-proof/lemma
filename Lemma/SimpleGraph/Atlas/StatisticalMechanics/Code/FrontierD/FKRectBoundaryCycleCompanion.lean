import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleCompanion
open StatMech StatMech.FrontierD


/--
[exists_other_nonzero_blackBoundaryCycle_in_primalCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleCompanion.lean)
-/
@[path]
private lemma exists_other_nonzero_blackBoundaryCycle_in_primalCluster_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {C : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hCcluster : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
  (hCne : fkRectBlackBoundaryCycleWinding R omega C ≠ 0) :
-- imply
  ∃ D : FKRectConfigurationBlackBoundaryCycle R omega, D ≠ C ∧ fkRectBlackBoundaryCycleInPrimalCluster R omega x D ∧ fkRectBlackBoundaryCycleWinding R omega D ≠ 0 := by
-- proof
  apply StatMech.FrontierD.exists_other_nonzero_blackBoundaryCycle_in_primalCluster R omega x C hCcluster hCne


-- created on 2026-10-23
