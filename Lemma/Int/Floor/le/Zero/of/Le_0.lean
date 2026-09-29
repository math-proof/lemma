import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ≤ 0) :
-- imply
  ⌊x⌋ ≤ 0 := by
-- proof
  exact Int.floor_nonpos h


-- created on 2026-09-27
