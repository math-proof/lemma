import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[path]
private lemma main
  (x : ℝ) :
-- imply
  deriv Real.tan x = Real.sec x ^ 2 := by
-- proof
  rw [Real.deriv_tan, Real.sec, div_pow, one_pow]


-- created on 2026-10-11
-- updated on 2026-10-17
