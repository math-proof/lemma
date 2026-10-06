import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  -- given
  (h : b ≤ a)
  -- imply
  : b - 1 < a := by
  -- proof
  omega

-- created on 2019-05-23
