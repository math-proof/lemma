import Lemma.Algebra.Eq_Nil.of.EqLength_0
open Algebra


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
