import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Int.fract x = x + ⌈-x⌉ := by
-- proof
  rw [Int.ceil_neg, Int.fract]
  push_cast
  ring


-- created on 2019-05-14
