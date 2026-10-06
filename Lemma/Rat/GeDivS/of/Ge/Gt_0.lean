import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h : b ≤ a)
  (hx : 0 < x)
  -- imply
  : b / x ≤ a / x := by
  -- proof
  exact div_le_div_of_nonneg_right h (le_of_lt hx)

-- created on 2019-05-22
