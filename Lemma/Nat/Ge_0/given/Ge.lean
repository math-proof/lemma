import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  -- given
  (h : 0 ≤ a - b)
  -- imply
  : b ≤ a := by
  -- proof
  exact le_of_sub_nonneg h

-- created on 2018-07-03
