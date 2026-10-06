import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  -- given
  (h : b < a)
  -- imply
  : b < a := by
  -- proof
  exact h

-- created on 2021-09-15
