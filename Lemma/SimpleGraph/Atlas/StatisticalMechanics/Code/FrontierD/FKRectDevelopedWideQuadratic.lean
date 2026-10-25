import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideQuadratic
open Set StatMech StatMech.FrontierD


/--
[fkRectDevelopedSquare_dualHorizontalCompl_subset_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideQuadratic.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_dualHorizontalCompl_subset_vertical_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height) :
-- imply
  fkRectDualEvent R (fkRectDevelopedSquareHorizontalCrossingEvent R n)ᶜ ⊆ fkRectDevelopedSquareVerticalCrossingEvent R n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_dualHorizontalCompl_subset_vertical R n hn hwidth hheight

/--
[fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideQuadratic.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (1 + q) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q R n hn hwidth hheight hq

/--
[fkRectCritical_threeByOneHorizontal_sq_div_one_add_q_sq_le_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideQuadratic.lean)
-/
@[path]
private lemma fkRectCritical_threeByOneHorizontal_sq_div_one_add_q_sq_le_vertical_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) ^ 2 / (1 + q ^ 2) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_threeByOneHorizontal_sq_div_one_add_q_sq_le_vertical R n hn hwidth hheight hq

/--
[fkRectCritical_threeByOneVerticalMass_ge_one_div_eight_mul_pow_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideQuadratic.lean)
-/
@[path]
private lemma fkRectCritical_threeByOneVerticalMass_ge_one_div_eight_mul_pow_six_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (8 * q ^ 6) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_threeByOneVerticalMass_ge_one_div_eight_mul_pow_six R n hn hwidth hheight hq


-- created on 2026-10-23
