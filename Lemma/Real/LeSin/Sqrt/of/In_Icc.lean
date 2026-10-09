import sympy.functions.elementary.trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Icc 0 (Real.pi / 4)) :
-- imply
  Real.sin x ≤ Real.sqrt (2 * x / Real.pi) := by
-- proof
  obtain ⟨hx0, hx1⟩ := h
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have hcos : 1 - 2 / Real.pi * (2 * x) ≤ Real.cos (2 * x) := by
    apply Real.one_sub_mul_le_cos
    ·
      linarith
    ·
      linarith
  rw [Real.le_sqrt hsin (by positivity)]
  rw [Real.sin_sq_eq_half_sub]
  rw [le_div_iff₀ hpi]
  have h2 : (1 - 2 / Real.pi * (2 * x)) * Real.pi = Real.pi - 4 * x := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_right hcos hpi.le
  rw [h2] at h3
  have h4 : (1 / 2 - Real.cos (2 * x) / 2) * Real.pi = (Real.pi - Real.cos (2 * x) * Real.pi) / 2 := by
    ring
  rw [h4]
  linarith


-- created on 2026-10-07
