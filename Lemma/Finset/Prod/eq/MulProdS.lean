import Lemma.Algebra.Prod.eq.Prod_Pow_Bool
import Lemma.Finset.Prod_Mul.eq.MulProdS
import Lemma.Algebra.Pow_Add.eq.MulPowS
import Lemma.Set.BoolIn.eq.AddBoolSIn
open Algebra Set Finset


@[main]
private lemma main
  [Fintype ι] [DecidableEq ι]
  [CommMonoid α]
-- given
  (A B : Finset ι)
  (f : ι → α) :
-- imply
  ∏ x ∈ A, f x = (∏ x ∈ A ∩ B, f x) * ∏ x ∈ A \ B, f x := by
-- proof
  rw [Prod.eq.Prod_Pow_Bool]
  rw [Prod.eq.Prod_Pow_Bool (s := A ∩ B)]
  rw [Prod.eq.Prod_Pow_Bool (s := A \ B)]
  rw [MulProdS.eq.Prod_Mul]
  simp only [MulPowS.eq.Pow_Add]
  simp only [AddBoolSIn.eq.BoolIn.fin]


-- created on 2025-04-30
-- updated on 2025-05-01
