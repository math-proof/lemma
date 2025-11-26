import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (n : α) :
-- imply
  (s.set i (n * s[i])).prod = (s.take i).prod * (n * (s.drop i).prod) := by
-- proof
  rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength h]
  apply EqMulS.of.Eq.left
  rw [MulMul.eq.Mul_Mul]
  apply EqMulS.of.Eq.left
  apply Mul_ProdDrop_Add_1.eq.ProdDrop.of.Lt_Length


-- created on 2025-07-17
