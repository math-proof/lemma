import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingAlgebra
open StatMech StatMech.FrontierD


/--
[crossing_vertical_ge_one_div_eight_mul_pow_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingAlgebra.lean)
-/
@[path]
private lemma crossing_vertical_ge_one_div_eight_mul_pow_six_eq
  {q H V : Real}
-- given
  (hq : 1 ≤ q)
  (hV : 0 ≤ V)
  (hsum : 1 ≤ V + q ^ 2 * H)
  (hquadratic : H ^ 2 / (1 + q ^ 2) ≤ V) :
-- imply
  1 / (8 * q ^ 6) ≤ V := by
-- proof
  apply StatMech.FrontierD.crossing_vertical_ge_one_div_eight_mul_pow_six hq hV hsum hquadratic

/--
[crossing_hard_ge_one_div_eight_mul_pow_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingAlgebra.lean)
-/
@[path]
private lemma crossing_hard_ge_one_div_eight_mul_pow_two_eq
  {q hard easy : Real}
-- given
  (hq : 1 ≤ q)
  (hhard : 0 ≤ hard)
  (hsum : 1 ≤ easy + q ^ 2 * hard)
  (hquadratic : easy ^ 2 / (1 + q ^ 2) ≤ hard) :
-- imply
  1 / (8 * q ^ 2) ≤ hard := by
-- proof
  apply StatMech.FrontierD.crossing_hard_ge_one_div_eight_mul_pow_two hq hhard hsum hquadratic

/--
[crossing_hard_ge_of_square_seed_and_sixth_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingAlgebra.lean)
-/
@[path]
private lemma crossing_hard_ge_of_square_seed_and_sixth_power_eq
  {q square hard : Real}
-- given
  (hq : 1 ≤ q)
  (hseed : 1 / (1 + q) ≤ square)
  (hrsw : square ^ 6 / (16 * (1 + q)) ≤ hard) :
-- imply
  1 / (16 * (1 + q) ^ 7) ≤ hard := by
-- proof
  apply StatMech.FrontierD.crossing_hard_ge_of_square_seed_and_sixth_power hq hseed hrsw

/--
[crossing_hard_ge_of_square_seed_and_sixth_power_qsq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingAlgebra.lean)
-/
@[path]
private lemma crossing_hard_ge_of_square_seed_and_sixth_power_qsq_eq
  {q square hard : Real}
-- given
  (hq : 1 ≤ q)
  (hseed : 1 / (1 + q) ≤ square)
  (hrsw : square ^ 6 / (16 * (1 + q ^ 2)) ≤ hard) :
-- imply
  (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2)) ≤ hard := by
-- proof
  apply StatMech.FrontierD.crossing_hard_ge_of_square_seed_and_sixth_power_qsq hq hseed hrsw


-- created on 2026-10-23
