import Lemma.List.EqDrop_0
open List


@[main]
private lemma main
-- given
  (a : List α)
  (h : n = 0) :
-- imply
  a.drop n = a :=
-- proof
  h.symm.subst (motive := fun n => a.drop n = a) (EqDrop_0 a)


-- created on 2025-06-16
-- updated on 2026-07-12
