module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.chi_sq
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x * chi S x = 1 := by
-- proof
  have h := chi_sq (S := S) (x := x)
  linarith [sq_abs (chi S x), h, sq_nonneg (chi S x)]


theorem BooleanFourier.chi_mul_self
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x * chi S x = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
