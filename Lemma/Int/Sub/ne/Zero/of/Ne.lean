import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℤ}
  -- given
  (h : x ≠ y)
  -- imply
  : x - y ≠ 0 := by
  -- proof
  exact sub_ne_zero.mpr h

-- created on 2018-11-12
