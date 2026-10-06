import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x t : ℝ}
  -- given
  (hx : 0 < x)
  (ht : t < 1)
  -- imply
  : t * x < x := by
  -- proof
  have h : t * x < 1 * x := mul_lt_mul_of_pos_right ht hx
  simpa using h

-- created on 2019-06-16
