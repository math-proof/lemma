import Lemma.List.ProdSet.eq.MulMulProd__Prod.of.Lt_Length
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
  rw [ProdSet.eq.MulMulProd__Prod.of.Lt_Length h]
  apply Dvd_Mul.of.Dvd.left
  apply Dvd_Mul


-- created on 2025-07-12
