import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a : ℤ}
  -- imply
  : x < a ↔ x + 1 ≤ a := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
