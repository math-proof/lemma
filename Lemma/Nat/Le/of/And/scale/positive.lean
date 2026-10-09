import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ}
  -- given
  (hle : a ≤ b)
  (hpos : 0 < c)
  -- imply
  : a * c ≤ b * c := by
  -- proof
  exact mul_le_mul_of_nonneg_right hle (le_of_lt hpos)

-- created on 2023-03-26
