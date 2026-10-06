import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
  -- given
  (hlt : x < 0)
  (hle : a ≤ b)
  -- imply
  : x < 0 ∧ b * x ≤ a * x := by
  -- proof
  exact ⟨hlt, mul_le_mul_of_nonpos_right hle (le_of_lt hlt)⟩

-- created on 2023-10-03
