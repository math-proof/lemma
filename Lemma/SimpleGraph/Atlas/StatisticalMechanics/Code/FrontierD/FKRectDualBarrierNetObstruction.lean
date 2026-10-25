import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part5
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectDualConfigurationEquiv_dualPullbackConfiguration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean)
-/
@[path]
private lemma fkRectDualConfigurationEquiv_dualPullbackConfiguration_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectDualConfigurationEquiv R (fkRectDualPullbackConfiguration R eta) = eta := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfigurationEquiv_dualPullbackConfiguration R eta

/--
[fkRectDualBarrierNetObstruction_dual_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean)
-/
@[path]
private lemma fkRectDualBarrierNetObstruction_dual_mem_source_eq
  {R : FKRectTorus} :
-- imply
  fkRectDualConfigurationEquiv R (fkRectDualBarrierNetObstructionConfiguration R) ∈ fkRectSourceLeftBarrier R 1 (fkRectUnitLeftBarrierGap R) := by
-- proof
  apply StatMech.FrontierD.fkRectDualBarrierNetObstruction_dual_mem_source R

/--
[fkRectDualBarrierNetObstruction_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean)
-/
@[path]
private lemma fkRectDualBarrierNetObstruction_hasNet_eq
  {R : FKRectTorus} :
-- imply
  FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) := by
-- proof
  apply StatMech.FrontierD.fkRectDualBarrierNetObstruction_hasNet R

/--
[fkRectDualBarrierNetObstruction_hasNet_and_dualNoCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean)
-/
@[path]
private lemma fkRectDualBarrierNetObstruction_hasNet_and_dualNoCrossing_eq
  {R : FKRectTorus} :
-- imply
  FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) ∧ fkRectDualBarrierNetObstructionConfiguration R ∈ fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R 1) := by
-- proof
  apply StatMech.FrontierD.fkRectDualBarrierNetObstruction_hasNet_and_dualNoCrossing R


-- created on 2026-10-23
