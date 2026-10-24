import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.OneArm
open Real StatMech StatMech.RSW StatMech.RSW.OneArm


/--
[roa_eps_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_eps_pos_eq
  {c : ℝ}
-- given
  (hc0 : 0 < c)
  (hc1 : c < 1) :
-- imply
  0 < roa_eps c := by
-- proof
  apply StatMech.RSW.OneArm.roa_eps_pos hc0 hc1

/--
[roa_one_sub_c_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_one_sub_c_eq_eq
  {c : ℝ}
-- given
  (_hc0 : 0 < c)
  (hc1 : c < 1) :
-- imply
  (1 - c) = (2 : ℝ) ^ (-(roa_eps c)) := by
-- proof
  apply StatMech.RSW.OneArm.roa_one_sub_c_eq _hc0 hc1

/--
[roa_geometricLog_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_geometricLog_polynomial_eq
  {a : ℕ → ℝ}
  {c : ℝ}
-- given
  (hc0 : 0 < c)
  (hc1 : c < 1)
  (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
-- imply
  ∀ n, 1 ≤ n → a n ≤ (2 : ℝ) ^ (roa_eps c) * (n : ℝ) ^ (-(roa_eps c)) := by
-- proof
  apply StatMech.RSW.OneArm.roa_geometricLog_polynomial a hc0 hc1 hann

/--
[roa_one_arm_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_one_arm_polynomial_eq
  {a : ℕ → ℝ}
  {c : ℝ}
-- given
  (hc0 : 0 < c)
  (hc1 : c < 1)
  (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
-- imply
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → a n ≤ C * (n : ℝ) ^ (-ε) := by
-- proof
  apply StatMech.RSW.OneArm.roa_one_arm_polynomial a hc0 hc1 hann

/--
[roa_polynomial_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_polynomial_tendsto_zero_eq
  {ε C : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.RSW.OneArm.roa_polynomial_tendsto_zero hε

/--
[roa_one_arm_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean)
-/
@[path]
private lemma roa_one_arm_tendsto_zero_eq
  {a : ℕ → ℝ}
  {c : ℝ}
-- given
  (hc0 : 0 < c)
  (hc1 : c < 1)
  (hnn : ∀ n, 0 ≤ a n)
  (hann : ∀ n, 1 ≤ n → a n ≤ (1 - c) ^ (Nat.log 2 n)) :
-- imply
  Filter.Tendsto a Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.RSW.OneArm.roa_one_arm_tendsto_zero a hc0 hc1 hnn hann


-- created on 2026-10-23
