import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
  -- imply
  : a ≤ b ↔ a < b + 1 := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
