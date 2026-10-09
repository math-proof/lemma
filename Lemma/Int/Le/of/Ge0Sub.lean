import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℤ}
  -- given
  (h : x - y ≤ 0)
  -- imply
  : x ≤ y := by
  -- proof
  exact le_of_sub_nonpos h

-- created on 2018-06-16
