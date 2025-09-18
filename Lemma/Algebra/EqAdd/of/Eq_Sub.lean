import Lemma.Algebra.EqSub.is.Eq_Add
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x a b : α}
-- given
  (h : a = x - b) :
-- imply
  a + b = x :=
-- proof
  (Eq_Add.of.EqSub h.symm).symm


-- created on 2024-11-27
