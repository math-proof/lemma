import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.MulMul
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {v : List α}
-- given
  (i : Fin v.length)
  (t : α) :
-- imply
  (v.set i (v[i] * t)).prod = v.prod * t := by
-- proof
  rw [List.prod_set]
  simp
  rw [MulMul.eq.Mul_Mul]
  rw [MulMul.comm]
  rw [Mul_Mul.eq.MulMul]
  apply EqMulS.of.Eq
  rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.Lt_Length]
  rw [← Prod.eq.MulProdTake__ProdDrop]


-- created on 2025-06-08
