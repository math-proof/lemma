import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- given
  (h : a = b)
  -- imply
  : a < b + 1 := by
  -- proof
  linarith

-- created on 2021-12-27
