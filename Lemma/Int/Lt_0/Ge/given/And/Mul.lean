import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
  -- given
  (hlt : x < 0)
  (hge : b ≤ a)
  -- imply
  : x < 0 ∧ a * x ≤ b * x := by
  -- proof
  exact ⟨hlt, mul_le_mul_of_nonpos_right hge (le_of_lt hlt)⟩

-- created on 2023-10-03
