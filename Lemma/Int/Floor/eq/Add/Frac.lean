import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  (⌊x⌋ : ℝ) = x - Int.fract x := by
-- proof
  exact (Int.self_sub_fract x).symm


-- created on 2019-05-11
