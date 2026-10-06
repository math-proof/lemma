import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h : min a b < x)
  -- imply
  : a < x ∨ b < x := by
  -- proof
  exact min_lt_iff.mp h

-- created on 2022-01-02
