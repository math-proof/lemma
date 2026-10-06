import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  -- imply
  : b < a ↔ b + 1 ≤ a := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
