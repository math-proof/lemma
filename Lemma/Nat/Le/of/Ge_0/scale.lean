import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x t : ℝ}
  -- given
  (hx : 0 ≤ x)
  (ht : t ≤ 1)
  -- imply
  : t * x ≤ x := by
  -- proof
  have h : t * x ≤ 1 * x := mul_le_mul_of_nonneg_right ht hx
  simpa using h

-- created on 2019-06-16
