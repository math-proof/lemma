import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  ⌊x⌋ ≤ ⌊y⌋ := by
-- proof
  exact Int.floor_mono h


-- created on 2026-09-27
