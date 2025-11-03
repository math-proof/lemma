import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DvdProdSDrop.of.Ge
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.Mul_ProdDrop_2
import Lemma.Nat.Dvd_Mul.of.Dvd
import stdlib.List.Basic
open List Nat


@[main]
private lemma main
  [CommMonoid Z]
-- given
  (h : d > i)
  (s : List Z) :
-- imply
  (s.drop d).prod ∣ (s.eraseIdx i).prod := by
-- proof
  rw [Prod.eq.MulProdS (s.eraseIdx i) (d - 1)]
  rw [DropEraseIdx.eq.Drop.of.Le (by omega)]
  rw [EqAddSub.of.Ge (by omega)]
  apply Dvd_Mul


-- created on 2025-11-03
