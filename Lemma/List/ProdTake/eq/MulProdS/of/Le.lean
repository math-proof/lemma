import stdlib.List
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.List.DropTake.eq.TakeDrop
open Algebra List


@[main]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : i ≤ j) :
-- imply
  (v.take j).prod = (v.take i).prod * (v.slice i j).prod := by
-- proof
  unfold List.slice List.array_slice
  unfold Function.comp
  rw [Prod.eq.MulProdTake__ProdDrop (v.take j) i]
  rw [TakeTake.eq.Take.of.Ge (by assumption)]
  apply EqMulS.of.Eq.left
  rw [DropTake.eq.TakeDrop]


-- created on 2025-06-14
-- updated on 2025-06-20
