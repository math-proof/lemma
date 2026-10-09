import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℤ}
  {y : ℝ}
-- given
  (h : x < y) :
-- imply
  x ≤ ⌊y⌋ := by
-- proof
  exact Int.le_floor.mpr h.le


-- created on 2019-10-02
