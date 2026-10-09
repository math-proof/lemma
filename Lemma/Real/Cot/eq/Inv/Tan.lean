import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.cot x = 1 / Real.tan x := by
  -- proof
  simp [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]

-- created on 2023-11-26
