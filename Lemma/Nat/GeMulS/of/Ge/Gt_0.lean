import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hx : 0 < x)
  (hge : b ≤ a)
  -- imply
  : b * x ≤ a * x := by
  -- proof
  exact mul_le_mul_of_nonneg_right hge (le_of_lt hx)

-- created on 2020-02-03
