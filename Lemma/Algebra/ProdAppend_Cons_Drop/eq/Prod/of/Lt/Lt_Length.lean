import Lemma.Algebra.ProdAppend.eq.MulProdS
import Lemma.Algebra.ProdCons.eq.Mul_Length
import Lemma.Algebra.MulMul
import Lemma.Algebra.ProdTake_Add_1.eq.MulProdTake.of.Lt_Length
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.ProdDrop.eq.Mul_ProdDrop.of.Lt_Length
import Lemma.Algebra.ProdTake.eq.MulProdS.of.Le
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
open Algebra


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
  rw [ProdAppend.eq.MulProdS, ProdAppend.eq.MulProdS]
  rw [ProdCons.eq.Mul_Length, ProdCons.eq.Mul_Length]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (c := a[i])]
  rw [← ProdTake_Add_1.eq.MulProdTake.of.Lt_Length (by linarith)]
  rw [Mul_Mul.eq.MulMul]
  rw [MulMul.comm (b := a[j])]
  rw [MulMul.eq.Mul_Mul]
  rw [← ProdDrop.eq.Mul_ProdDrop.of.Lt_Length (by assumption)]
  rw [← ProdTake.eq.MulProdS.of.Le (by assumption)]
  simp [Prod.eq.MulProdTake__ProdDrop]


-- created on 2025-06-14
