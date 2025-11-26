import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i < s.length)
  (a : α) :
-- imply
  a ∣ (s.set i a).prod := by
-- proof
  rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength h]
  apply Dvd_Mul.of.Dvd
  apply Dvd_Mul.left


-- created on 2025-07-12
