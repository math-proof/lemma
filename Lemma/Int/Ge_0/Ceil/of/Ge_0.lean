import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  ⌈x⌉ ≥ 0 := by
-- proof
  exact Int.ceil_nonneg h


-- created on 2019-03-11
