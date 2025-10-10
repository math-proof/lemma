import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.DropTake.eq.ListGet.of.Lt_Length
open List Nat


@[main]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.take (i + 1)).prod = (v.take i).prod * v[i] := by
-- proof
  have := Prod.eq.MulProdTake__ProdDrop (v.take (i + 1)) i
  rw [this]
  rw [TakeTake.eq.Take.of.Ge (by linarith)]
  apply EqMulS.of.Eq.left
  rw [DropTake.eq.ListGet.of.Lt_Length (by assumption)]
  simp


-- created on 2025-06-14
