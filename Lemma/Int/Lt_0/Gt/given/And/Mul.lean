import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
  -- given
  (hlt : x < 0)
  (hgt : b < a)
  -- imply
  : x < 0 ∧ a * x < b * x := by
  -- proof
  exact ⟨hlt, mul_lt_mul_of_neg_right hgt hlt⟩

-- created on 2023-10-03
