import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hgt : 0 < x)
  (hle : a ≤ b)
  -- imply
  : 0 < x ∧ a * x ≤ b * x := by
  -- proof
  exact ⟨hgt, mul_le_mul_of_nonneg_right hle (le_of_lt hgt)⟩

-- created on 2023-10-03
