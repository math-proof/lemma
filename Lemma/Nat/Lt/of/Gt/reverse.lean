import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
  -- given
  (h : x < a)
  -- imply
  : a > x := by
  -- proof
  exact h

-- created on 2019-10-29
