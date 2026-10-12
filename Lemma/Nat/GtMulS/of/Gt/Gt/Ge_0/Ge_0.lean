import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : b < a)
  (h₁ : y < x)
  (hb : 0 ≤ b)
  (hy : 0 ≤ y) :
-- imply
  b * y < a * x := by
-- proof
  have hxpos : 0 < x := by linarith
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt h₁) hb)
  exact mul_lt_mul_of_pos_right h₀ hxpos


-- created on 2018-07-06
