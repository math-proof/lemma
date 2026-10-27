/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Def.Analysis.SpecialFunctions.ExpSubOneMittagLeffler.Part3
/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/


namespace MetaMathlibExt

open scoped BigOperators

open Complex

noncomputable section

theorem expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder (N : ℕ) (v : ℝ) :
    expSubOneRemainder N v = oneDivExpSubOneLaurentRemainder N v := by
  by_cases hv : v = 0
  · subst v
    simp [expSubOneRemainder, expSubOneRemainderTerm, oneDivExpSubOneLaurentRemainder]
  · simp only [oneDivExpSubOneLaurentRemainder, hv, ↓reduceIte]
    exact (expSubOneKernel_eq N v hv).symm

/-- The analytic Laurent remainder of the Bose-Einstein kernel is differentiable. -/
theorem differentiable_oneDivExpSubOneLaurentRemainder (N : ℕ) :
    Differentiable ℝ (oneDivExpSubOneLaurentRemainder N) := by
  have hfun : oneDivExpSubOneLaurentRemainder N = expSubOneRemainder N := by
    funext v
    exact (expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder N v).symm
  rw [hfun]
  exact fun v => (expSubOneRemainder_hasDerivAt N v).differentiableAt

/-- The analytic Laurent remainder is bounded by its first omitted odd power. -/
theorem oneDivExpSubOneLaurentRemainder_abs_le (N : ℕ) (v : ℝ) :
    |oneDivExpSubOneLaurentRemainder N v| ≤
      (2 * (2 * N + 3 : ℕ) *
        ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
        |v| ^ (2 * N + 1) := by
  rw [← expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder]
  simpa only [expSubOneBound, expSubOnePole] using expSubOneRemainder_abs_le_bound N v

/-- The derivative of the analytic Laurent remainder is bounded by the preceding even power. -/
theorem abs_deriv_oneDivExpSubOneLaurentRemainder_le (N : ℕ) (v : ℝ) :
    |deriv (oneDivExpSubOneLaurentRemainder N) v| ≤
      (2 * (2 * N + 3 : ℕ) *
        ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
        |v| ^ (2 * N) := by
  have hfun : oneDivExpSubOneLaurentRemainder N = expSubOneRemainder N := by
    funext y
    exact (expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder N y).symm
  rw [hfun, (expSubOneRemainder_hasDerivAt N v).deriv]
  simpa only [expSubOneBound, expSubOnePole] using expSubOneRemainder_deriv_abs_le_bound N v

/-- The truncated Laurent expansion of the Bose-Einstein kernel has a global
`|v| ^ (2 * N + 1)` remainder bound away from its removable singularity. -/
theorem abs_one_div_exp_sub_one_sub_laurent_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, v ≠ 0 →
      |1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
          ∑ n ∈ Finset.range N,
            (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
              v ^ (2 * n + 1)| ≤
        C * |v| ^ (2 * N + 1) := by
  let C := 2 * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by norm_num) (tsum_nonneg fun m =>
      inv_nonneg.mpr (pow_nonneg (expSubOnePole_pos m).le _))
  refine ⟨C, hC, fun v hv => ?_⟩
  rw [expSubOneKernel_eq N v hv]
  calc
    |expSubOneRemainder N v| ≤
        2 * |v| ^ (2 * N + 1) *
          ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      expSubOneRemainder_abs_le N v
    _ = C * |v| ^ (2 * N + 1) := by
      unfold C
      ring

end
end MetaMathlibExt
