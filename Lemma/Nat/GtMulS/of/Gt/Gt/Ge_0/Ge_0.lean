import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
  -- given
  (h1 : b < a)
  (h2 : y < x)
  (hb : 0 ≤ b)
  (hy : 0 ≤ y)
  -- imply
  : b * y < a * x := by
  -- proof
  have hxpos : 0 < x := by linarith
  have h3 : b * x < a * x := mul_lt_mul_of_pos_right h1 hxpos
  have h4 : b * y ≤ b * x := mul_le_mul_of_nonneg_left (le_of_lt h2) hb
  exact lt_of_le_of_lt h4 h3

-- created on 2018-07-06
