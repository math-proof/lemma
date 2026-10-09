import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- imply
  : x < a ↔ a ≥ x + 1 := by
  -- proof
  constructor <;> omega

-- created on 2022-01-28
