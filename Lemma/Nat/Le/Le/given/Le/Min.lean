import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h1 : x ≤ a)
  (h2 : x ≤ b)
  -- imply
  : x ≤ min a b := by
  -- proof
  exact le_min h1 h2

-- created on 2022-01-03
