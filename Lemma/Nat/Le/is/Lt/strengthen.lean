import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  -- imply
  : a ≤ b ↔ a - 1 < b := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
