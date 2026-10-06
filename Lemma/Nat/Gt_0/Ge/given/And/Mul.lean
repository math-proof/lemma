import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hgt : 0 < x)
  (hge : b ≤ a)
  -- imply
  : 0 < x ∧ b * x ≤ a * x := by
  -- proof
  exact ⟨hgt, mul_le_mul_of_nonneg_right hge (le_of_lt hgt)⟩

-- created on 2023-10-03
