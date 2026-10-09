import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
  -- given
  (h : y < x)
  -- imply
  : y ≤ x := by
  -- proof
  exact le_of_lt h

-- created on 2019-05-30
