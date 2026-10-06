import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := by
-- proof
  have h := Real.cosh_sq_sub_sinh_sq x
  linarith


-- created on 2023-11-26
