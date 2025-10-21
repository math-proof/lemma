import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.Lt_Length
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {v : List α}
-- given
  (h : i < v.length)
  (a : α) :
-- imply
  a ∣ (v.set i a).prod := by
-- proof
  rw [ProdSet.eq.MulProd_Mul_Prod.of.Lt_Length h]
  apply Dvd_Mul.of.Dvd
  apply Dvd_Mul.left


-- created on 2025-07-12
