import Mathlib
import sympy.Basic


/--
[Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff.lean)
-/
@[main]
private lemma main
  :
-- imply
  (∀ X : ℝ, |1 - (Real.exp X)⁻¹| = Real.exp (-X) * |1 - Real.exp X|) ∧
    (∀ X : ℝ, |1 - (-Real.exp X)⁻¹| = 1 + Real.exp (-X)) ∧
    (∀ X : ℝ, 0 < 1 + Real.exp (-X)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ => 1 + Real.exp (-X)) := by
-- proof
  refine ⟨fun X => ?_, fun X => ?_, fun X => by positivity, ?_⟩
  · rw [← Real.exp_neg]
    have h : (1 : ℝ) - Real.exp (-X) = Real.exp (-X) * (Real.exp X - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [h, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
  · rw [inv_neg, sub_neg_eq_add, ← Real.exp_neg, abs_of_pos (by positivity)]
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)


-- created on 2026-10-05
