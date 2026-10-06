import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
  -- given
  (h : n % 2 = 1)
  -- imply
  : (n + 1) % 2 = 0 := by
  -- proof
  omega

-- created on 2023-05-30
