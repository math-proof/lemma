import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  ⌊x⌋ < 0 := by
-- proof
  exact Int.floor_lt.mpr (by exact_mod_cast h)


-- created on 2020-01-20
