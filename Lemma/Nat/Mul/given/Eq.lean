import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
  -- given
  (h : a = b)
  -- imply
  : a * x = b * x := by
  -- proof
  exact congr_arg (· * x) h

-- created on 2019-11-26
