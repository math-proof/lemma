import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : ℝ}
-- given
  (h : a = 0) :
-- imply
  a ≠ 1 := by
-- proof
  rw [h]
  simp


-- created on 2018-03-20
