import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : ⌊x⌋ = 0) :
-- imply
  x ∈ Set.Ico 0 1 := by
-- proof
  exact Int.floor_eq_zero_iff.mp h


-- created on 2020-01-19
