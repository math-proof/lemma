import Lemma.List.Take_0.eq.Nil
open List


@[main]
private lemma main
-- given
  (a : List α)
  (h : i = 0) :
-- imply
  a.take i = .nil :=
-- proof
  h.symm.subst (motive := fun i => a.take i = .nil) (Take_0.eq.Nil a)


-- created on 2025-06-16
