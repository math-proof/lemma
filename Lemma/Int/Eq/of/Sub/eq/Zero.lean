import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : 0 = a - b) :
-- imply
  a = b := by
-- proof
  exact sub_eq_zero.mp h.symm


-- created on 2018-05-09
