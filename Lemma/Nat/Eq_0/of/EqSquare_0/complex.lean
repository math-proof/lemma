import Mathlib.Data.Complex.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
  -- given
  (h : x ^ 2 = 0)
  -- imply
  : x = 0 := by
  -- proof
  have h2 : x * x = 0 := by simpa [pow_two] using h
  exact mul_self_eq_zero.mp h2

-- created on 2018-11-11
