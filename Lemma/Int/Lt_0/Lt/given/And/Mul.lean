import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
  -- given
  (hlt : x < 0)
  (hlt2 : a < b)
  -- imply
  : x < 0 ∧ b * x < a * x := by
  -- proof
  exact ⟨hlt, mul_lt_mul_of_neg_right hlt2 hlt⟩

-- created on 2023-10-03
