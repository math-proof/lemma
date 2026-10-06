import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hgt : 0 < x)
  (hgt2 : b < a)
  -- imply
  : 0 < x ∧ b * x < a * x := by
  -- proof
  exact ⟨hgt, mul_lt_mul_of_pos_right hgt2 hgt⟩

-- created on 2023-10-03
