import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  -- given
  (h : 0 ≤ x - y)
  -- imply
  : y ≤ x := by
  -- proof
  exact le_of_sub_nonneg h

-- created on 2018-07-03
