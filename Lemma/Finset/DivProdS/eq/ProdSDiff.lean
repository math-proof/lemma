import Lemma.Finset.Prod.eq.MulProdS
import sympy.Basic
open Finset


@[main]
private lemma main
  [Fintype ι] [DecidableEq ι]
  [CommGroup α]
-- given
  (A B : Finset ι)
  (f : ι → α) :
-- imply
  (∏ x ∈ A, f x) / (∏ x ∈ A ∩ B, f x) = ∏ x ∈ A \ B, f x := by
-- proof
  rw [Prod.eq.MulProdS A B f]
  apply mul_div_cancel_left


-- created on 2020-02-01
