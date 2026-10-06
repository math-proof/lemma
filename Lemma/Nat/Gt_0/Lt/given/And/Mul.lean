import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hgt : 0 < x)
  (hlt : a < b)
  -- imply
  : 0 < x ∧ a * x < b * x := by
  -- proof
  exact ⟨hgt, mul_lt_mul_of_pos_right hlt hgt⟩

-- created on 2023-10-03
