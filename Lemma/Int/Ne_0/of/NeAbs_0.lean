import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : |x| ≠ 0) :
-- imply
  x ≠ 0 := by
-- proof
  exact abs_ne_zero.mp h


-- created on 2018-08-01
