import Mathlib.Analysis.Normed.Module.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {x y t : E}
  {α : ℝ}
-- given
  (hα : α > 0)
  (h : ‖x - y‖ > 0) :
-- imply
  ‖(1 + α)⁻¹ • (x + α • t) - (1 + α)⁻¹ • (y + α • t)‖ < ‖x - y‖ := by
-- proof
  rw [← smul_sub, add_sub_add_right_eq_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h₁ : (1 + α)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  calc (1 + α)⁻¹ * ‖x - y‖ < 1 * ‖x - y‖ := mul_lt_mul_of_pos_right h₁ h
    _ = ‖x - y‖ := one_mul _


-- created on 2021-09-23
