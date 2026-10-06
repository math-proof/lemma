import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℤ}
  -- given
  (h : x ≠ 0)
  -- imply
  : 0 < |x| := by
  -- proof
  exact abs_pos.mpr h

-- created on 2018-06-16
