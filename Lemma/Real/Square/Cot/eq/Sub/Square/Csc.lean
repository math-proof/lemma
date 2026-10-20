import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sin x ≠ 0) :
-- imply
  Real.cot x ^ 2 = Real.csc x ^ 2 - 1 := by
-- proof
  rw [Real.cot_eq_cos_div_sin]
  simp only [Real.csc]
  field_simp [h]
  linarith [Real.sin_sq_add_cos_sq x]


-- created on 2023-10-03
-- updated on 2026-10-17
