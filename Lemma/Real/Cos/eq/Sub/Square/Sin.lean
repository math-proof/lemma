import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
  -- proof
  have : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  linarith

-- created on 2023-11-26
