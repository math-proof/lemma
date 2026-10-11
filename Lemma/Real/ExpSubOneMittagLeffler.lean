import Mathlib
import sympy.Basic
import sympy.functions.special.ExpSubOneMittagLeffler


/--
[ExpSubOneMittagLeffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean)
-/
@[path]
private lemma one_div_exp_sub_one_eq_tsum_eq
-- given
  (u : ℝ)
  (hu : u ≠ 0) :
-- imply
  1 / (Real.exp u - 1) = 1 / u - 1 / 2 +
    ∑' m : ℕ, 2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
-- proof
  apply MetaMathlibExt.one_div_exp_sub_one_eq_tsum u hu

/--
[ExpSubOneMittagLeffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean)
-/
@[path]
private lemma differentiable_one_div_exp_sub_one_laurent_remainder_is
-- given
  (N : ℕ) :
-- imply
  Differentiable ℝ (MetaMathlibExt.oneDivExpSubOneLaurentRemainder N) := by
-- proof
  apply MetaMathlibExt.differentiable_oneDivExpSubOneLaurentRemainder N

/--
[ExpSubOneMittagLeffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean)
-/
@[path]
private lemma one_div_exp_sub_one_laurent_remainder_abs_le_le
-- given
  (N : ℕ)
  (v : ℝ) :
-- imply
  |MetaMathlibExt.oneDivExpSubOneLaurentRemainder N v| ≤
    (2 * (2 * N + 3 : ℕ) *
      ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
      |v| ^ (2 * N + 1) := by
-- proof
  apply MetaMathlibExt.oneDivExpSubOneLaurentRemainder_abs_le N v

/--
[ExpSubOneMittagLeffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean)
-/
@[path]
private lemma abs_deriv_one_div_exp_sub_one_laurent_remainder_le_le
-- given
  (N : ℕ)
  (v : ℝ) :
-- imply
  |deriv (MetaMathlibExt.oneDivExpSubOneLaurentRemainder N) v| ≤
    (2 * (2 * N + 3 : ℕ) *
      ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
      |v| ^ (2 * N) := by
-- proof
  apply MetaMathlibExt.abs_deriv_oneDivExpSubOneLaurentRemainder_le N v

/--
[ExpSubOneMittagLeffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpSubOneMittagLeffler.lean)
-/
@[path]
private lemma abs_one_div_exp_sub_one_sub_laurent_le_is
-- given
  (N : ℕ) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, v ≠ 0 →
    |1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
        ∑ n ∈ Finset.range N,
          (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            v ^ (2 * n + 1)| ≤
      C * |v| ^ (2 * N + 1) := by
-- proof
  apply MetaMathlibExt.abs_one_div_exp_sub_one_sub_laurent_le N


-- created on 2026-10-11
