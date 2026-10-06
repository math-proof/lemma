import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  -- given
  (h : a * b = 0)
  -- imply
  : a = 0 ∨ b = 0 := by
  -- proof
  exact mul_eq_zero.mp h

-- created on 2019-11-26
