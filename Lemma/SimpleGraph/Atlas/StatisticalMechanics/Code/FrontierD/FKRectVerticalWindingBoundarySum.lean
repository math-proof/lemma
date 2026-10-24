import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingBoundarySum
open StatMech StatMech.FrontierD


/--
[fkMedialLoopCanonicalVerticalFlux_blackBoundaryCycleToLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingBoundarySum.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_blackBoundaryCycleToLoop_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectConfigurationBlackBoundaryCycle R omega} :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R omega fkMedialLoopCanonicalVerticalFlux pairing (fkMedialBlackBoundaryCycleToLoop pairing C) = -(fkRectBlackBoundaryCycleWinding R omega C).2 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_blackBoundaryCycleToLoop R omega C

/--
[fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingBoundarySum.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkMedialUnorientedVerticalWindingTotal (fkRectConfigurationToMedialPairing R omega) = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega, (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle R omega


-- created on 2026-10-23
