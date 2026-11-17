module

public import Theorem.List.ProdAppend.eq.MulProdS
public import Theorem.Nat.MulMul
public import Theorem.List.ProdTake_Add_1.eq.MulProdTake.of.GtLength
public import Theorem.Nat.MulMul.eq.Mul_Mul
public import Theorem.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
public import Theorem.List.ProdTake.eq.MulProdS.of.Ge

public section

open List Nat


public theorem List.ProdAppend_Cons_Drop.eq.Prod.of.Lt.GtLength
  [CommMonoid α]
  {s : List α}
  {i j : ℕ}
-- given
  (h_j : s.length > j)
  (h_i : i < j) :
-- imply
  (s.take i ++ s[j] :: s.slice (i + 1) j ++ s[i] :: s.drop (j + 1)).prod = s.prod := by
-- proof
  repeat rw [ProdAppend.eq.MulProdS]
  repeat rw [ProdCons.eq.Mul_Prod]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (c := s[i])]
  rw [← ProdTake_Add_1.eq.MulProdTake.of.GtLength (by linarith)]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (b := s[j])]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength (by assumption)]
  rw [← ProdTake.eq.MulProdS.of.Ge (by assumption)]
  simp


-- created on 2025-06-14
