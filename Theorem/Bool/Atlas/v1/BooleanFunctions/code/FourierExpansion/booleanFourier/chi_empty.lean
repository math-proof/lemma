module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.one_add_boolToReal_mul_boolToReal
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x : Fin n → Bool} :
-- imply
  chi ∅ x = 1 := by
-- proof
  simp [chi]


theorem BooleanFourier.chi_empty
  {n : ℕ}
  {x : Fin n → Bool} :
-- imply
  chi ∅ x = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
