import Lemma.List.Eq_Nil.is.EqLength_0
open List


@[main]
private lemma main
  {a : List.Vector α n}
-- given
  (h : a.length = 0) :
-- imply
  a.val = [] := by
-- proof
  apply Eq_Nil.of.EqLength_0
  simp_all


-- created on 2025-05-29
