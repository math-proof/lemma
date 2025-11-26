import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.MulMul
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.Prod.eq.MulProdS
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (t : α) :
-- imply
  (s.set i (s[i] * t)).prod = s.prod * t := by
-- proof
  rw [List.prod_set]
  simp
  rw [MulMul.eq.Mul_Mul]
  rw [MulMul.comm]
  rw [Mul_Mul.eq.MulMul]
  apply EqMulS.of.Eq
  rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength]
  rw [← Prod.eq.MulProdS]


-- created on 2025-06-08
