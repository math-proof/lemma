import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  ⌈x⌉ ≤ ⌊x⌋ + 1 := by
-- proof
  exact Int.ceil_le_floor_add_one x


-- created on 2019-10-02
