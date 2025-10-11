import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.Lt_Length
import Lemma.Algebra.Dvd_Mul.of.Dvd
import Lemma.Algebra.Dvd_Mul
open Algebra List


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
