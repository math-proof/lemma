import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
open Equiv Finset StatMech StatMech.FrontierD


/--
[sum_fkRectBlackBoundaryWeight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean)
-/
@[path]
private lemma sum_fkRectBlackBoundaryWeight_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (∑ d : FKMedialBlackDart R.medialTorus, fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R omega) d) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectBlackBoundaryWeight_eq_zero R omega

/--
[sum_fkRectBlackBoundaryCycleWinding_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean)
-/
@[path]
private lemma sum_fkRectBlackBoundaryCycleWinding_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (∑ C : FKRectConfigurationBlackBoundaryCycle R omega, fkRectBlackBoundaryCycleWinding R omega C) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectBlackBoundaryCycleWinding_eq_zero R omega

/--
[sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean)
-/
@[path]
private lemma sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (∑ C : FKRectConfigurationBlackBoundaryCycle R omega, (fkRectBlackBoundaryCycleWinding R omega C).2) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero R omega

/--
[fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectUnorientedVerticalWindingTotal R omega = 2 * fkRectPositiveVerticalBoundaryWindingTotal R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary R omega

/--
[fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega = fkRectPositiveVerticalBoundaryWindingTotal R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary R omega


-- created on 2026-10-23
