import Lemma.List.ProdTail.eq.MulProdTakeTail
import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (h : d > 0)
  (s : List α) :
-- imply
  s.tail.prod = (s.take d).tail.prod * (s.drop d).prod := by
-- proof
  rw [ProdTail.eq.MulProdTakeTail s (d - 1)]
  rw [← TailTake.eq.TakeTail]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-12-02
