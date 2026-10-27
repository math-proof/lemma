import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  (⌈x⌉ : ℝ) = Int.fract (-x) + x := by
-- proof
  rw [Int.fract, Int.floor_neg]
  push_cast
  ring


-- created on 2019-03-06
