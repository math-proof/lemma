import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  -- given
  (h : x - y < 0)
  -- imply
  : y > x := by
  -- proof
  linarith

-- created on 2019-05-30
