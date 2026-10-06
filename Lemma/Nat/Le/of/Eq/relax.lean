import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  -- given
  (h : a = b)
  -- imply
  : a ≤ b := by
  -- proof
  exact le_of_eq h

-- created on 2021-12-27
