import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  ⌈x⌉ > 0 := by
-- proof
  exact Int.ceil_pos.mpr h


-- created on 2019-08-12
