import Lemma.Algebra.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Length
import Lemma.Algebra.MulMul
import Lemma.List.ProdTake_Add_1.eq.MulProdTake.of.Lt_Length
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.List.ProdDrop.eq.Mul_ProdDrop.of.Lt_Length
import Lemma.List.ProdTake.eq.MulProdS.of.Le
open Algebra List


@[main]
private lemma main
  [CommMonoid α]
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : i < j)
  (h₁ : j < a.length) :
-- imply
  (a.take i ++ a[j] :: a.slice (i + 1) j ++ a[i] :: a.drop (j + 1)).prod = a.prod := by
-- proof
  repeat rw [ProdAppend.eq.MulProdS]
  repeat rw [ProdCons.eq.Mul_Length]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (c := a[i])]
  rw [← ProdTake_Add_1.eq.MulProdTake.of.Lt_Length (by linarith)]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (b := a[j])]
  rw [MulMul.eq.Mul_Mul]
  rw [← ProdDrop.eq.Mul_ProdDrop.of.Lt_Length (by assumption)]
  rw [← ProdTake.eq.MulProdS.of.Le (by assumption)]
  simp


-- created on 2025-06-14
