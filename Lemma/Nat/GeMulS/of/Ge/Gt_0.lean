import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (hx : 0 < x)
  (hge : b ≤ a) :
-- imply
  b * x ≤ a * x :=
-- proof
  mul_le_mul_of_nonneg_right hge (le_of_lt hx)


-- created on 2018-07-19
