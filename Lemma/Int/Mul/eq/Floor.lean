import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  -⌈x⌉ = ⌊-x⌋ := by
-- proof
  exact Int.floor_neg.symm


-- created on 2020-01-29
