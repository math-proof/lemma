import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- given
  (h : Real.cos x ≠ 0)
  -- imply
  : Real.sin x = Real.tan x * Real.cos x := by
  -- proof
  rw [Real.tan_eq_sin_div_cos]
  field_simp [h]


-- created on 2026-10-20
