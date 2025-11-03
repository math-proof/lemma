import stdlib.List
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.DropTake.eq.TakeDrop
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : i ≤ j) :
-- imply
  (s.take j).prod = (s.take i).prod * (s.slice i j).prod := by
-- proof
  unfold List.slice List.array_slice
  unfold Function.comp
  rw [Prod.eq.MulProdS (s.take j) i]
  rw [TakeTake.eq.Take.of.Ge (by assumption)]
  apply EqMulS.of.Eq.left
  rw [DropTake.eq.TakeDrop]


-- created on 2025-06-14
-- updated on 2025-06-20
