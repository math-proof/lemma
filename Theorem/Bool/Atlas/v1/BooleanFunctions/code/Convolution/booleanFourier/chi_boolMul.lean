module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Convolution.booleanFourier.boolToReal_xnor
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_boolMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Convolution.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)}
  {x y : Fin n → Bool} :
-- imply
  chi S (boolMul x y) = chi S x * chi S y := by
-- proof
  simp only [chi, boolMul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact boolToReal_xnor (a := x i) (b := y i)


theorem BooleanFourier.chi_boolMul
  {n : ℕ}
  {S : Finset (Fin n)}
  {x y : Fin n → Bool} :
-- imply
  chi S (boolMul x y) = chi S x * chi S y := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
