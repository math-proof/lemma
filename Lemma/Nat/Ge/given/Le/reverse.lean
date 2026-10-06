import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a : ℤ}
  -- given
  (h : a ≤ x)
  -- imply
  : a ≤ x := by
  -- proof
  exact h

-- created on 2019-05-24
