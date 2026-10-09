import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- given
  (hge : 0 ≤ x)
  (hne : x ≠ 0)
  -- imply
  : 0 < x := by
  -- proof
  exact lt_of_le_of_ne hge hne.symm

-- created on 2018-07-15
