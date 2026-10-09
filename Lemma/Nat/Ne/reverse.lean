import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- given
  (h : a ≠ b)
  -- imply
  : b ≠ a := by
  -- proof
  exact Ne.symm h

-- created on 2019-10-29
