import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  ⌈x⌉ ≤ 0 := by
-- proof
  exact Int.ceil_le.mpr (by push_cast; linarith)


-- created on 2020-01-18
