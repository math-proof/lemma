import Lemma.Int.Ne_Add.of.NeSub
open Int


@[main]
private lemma main
  [AddGroup α]
  {x a b: α}
-- given
  (h : a ≠ x - b) :
-- imply
  a + b ≠ x :=
-- proof
  (Ne_Add.of.NeSub h.symm).symm


-- created on 2024-11-27
