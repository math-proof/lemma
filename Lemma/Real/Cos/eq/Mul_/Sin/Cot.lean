import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- given
  (h : Real.sin x ≠ 0)
  -- imply
  : Real.cos x = Real.cot x * Real.sin x := by
  -- proof
  rw [Real.cot_eq_cos_div_sin]
  field_simp [h]

-- created on 2023-11-26
