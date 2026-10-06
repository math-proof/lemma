import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h : x < min a b)
  -- imply
  : x < a ∧ x < b := by
  -- proof
  exact lt_min_iff.mp h

-- created on 2022-01-03
