import Lemma.Int.EqSub.is.Eq_Add
open Int


@[main]
private lemma main
  [AddGroup α]
  {x a b : α}
-- given
  (h : a ≠ x - b) :
-- imply
  a + b ≠ x := by
-- proof
  symm
  apply Ne_Add.of.NeSub
  by_contra heq
  apply h heq.symm


-- created on 2024-11-27
-- updated on 2026-08-01
