module

public import Theorem.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
public import Theorem.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength

public section

open List Nat


@[comm]
public theorem List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (n : α) :
-- imply
  (s.set i (n * s[i])).prod = (s.take i).prod * (n * (s.drop i).prod) := by
-- proof
  rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength h]
  apply Mul.of.Eq.left
  rw [MulMul.eq.Mul_Mul]
  apply Mul.of.Eq.left
  apply Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength


-- created on 2025-07-17
