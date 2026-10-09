import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  x ≥ ⌊x⌋ := by
-- proof
  exact Int.floor_le x


-- created on 2019-09-19
