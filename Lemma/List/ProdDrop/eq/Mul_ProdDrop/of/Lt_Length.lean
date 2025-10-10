import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
open List Nat


@[main]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.drop i).prod = v[i] * (v.drop (i + 1)).prod := by
-- proof
  have := Prod.eq.MulProdTake__ProdDrop (v.drop i) 1
  rw [this]
  rw [DropDrop.eq.Drop_Add]
  apply EqMulS.of.Eq
  rw [TakeDrop.eq.ListGet.of.Lt_Length (by assumption)]
  simp


-- created on 2025-06-14
