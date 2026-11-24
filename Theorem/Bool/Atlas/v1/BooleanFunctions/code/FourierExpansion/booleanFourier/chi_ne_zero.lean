module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.chi_mul_self
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ≠ 0 := by
-- proof
  simp only [chi]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => boolToReal_ne_zero (b := x i))


theorem BooleanFourier.chi_ne_zero
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ≠ 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
