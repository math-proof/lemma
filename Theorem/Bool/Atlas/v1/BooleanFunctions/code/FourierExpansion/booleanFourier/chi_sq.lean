module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.chi_empty
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ^ 2 = 1 := by
-- proof
  simp only [chi, ← Finset.prod_pow]
  simp [boolToReal_sq]


theorem BooleanFourier.chi_sq
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ^ 2 = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
