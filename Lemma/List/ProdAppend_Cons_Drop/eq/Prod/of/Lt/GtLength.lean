import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.Nat.MulMul
import Lemma.List.ProdTake_Add_1.eq.MulProdTake.of.GtLength
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdTake.eq.MulProdS.of.Le
open List Nat


@[main]
private lemma main
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
  rw [← ProdTake.eq.MulProdS.of.Le (by assumption)]
  simp


-- created on 2025-06-14
