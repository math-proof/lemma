import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x b : ℤ}
  -- given
  (h : x = b)
  -- imply
  : b ≤ x := by
  -- proof
  exact le_of_eq h.symm

-- created on 2019-03-31
-- updated on 2023-11-11
