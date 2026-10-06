import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
  -- given
  (h : x < y)
  -- imply
  : x ≤ y := by
  -- proof
  exact le_of_lt h

-- created on 2021-09-15
