import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberBalance
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[sum_fkRectPrimalComponentBoundaryVerticalWinding_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberBalance.lean)
-/
@[path]
private lemma sum_fkRectPrimalComponentBoundaryVerticalWinding_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  fkRectPrimalComponentBoundaryVerticalWindingSum R omega K = 0 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectPrimalComponentBoundaryVerticalWinding_eq_zero R omega K

/--
[fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberBalance.lean)
-/
@[path]
private lemma fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  fkRectPrimalComponentBoundaryVerticalMass R omega K = 2 * fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalComponentBoundaryVerticalMass_eq_two_mul_positive R omega K

/--
[verticalBoundaryMassCutFiberBound_iff_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberBalance.lean)
-/
@[path]
private lemma verticalBoundaryMassCutFiberBound_iff_positive_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectVerticalBoundaryMassCutFiberBound R omega ↔ FKRectPositiveVerticalBoundaryCutFiberBound R omega := by
-- proof
  apply StatMech.FrontierD.verticalBoundaryMassCutFiberBound_iff_positive R omega


-- created on 2026-10-23
