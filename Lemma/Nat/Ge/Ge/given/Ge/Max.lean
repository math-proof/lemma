import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h1 : a ≤ x)
  (h2 : b ≤ x)
  -- imply
  : max a b ≤ x := by
  -- proof
  exact max_le h1 h2

-- created on 2022-01-03
