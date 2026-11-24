module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.boolToReal_not
open Finset BigOperators BooleanFourier Bool


public section

/--
[one_add_boolToReal_mul_boolToReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {a b : Bool} :
-- imply
  1 + boolToReal a * boolToReal b = if a = b then 2 else 0 := by
-- proof
  cases a <;> cases b <;> simp [boolToReal] <;> norm_num


theorem BooleanFourier.one_add_boolToReal_mul_boolToReal
  {a b : Bool} :
-- imply
  1 + boolToReal a * boolToReal b = if a = b then 2 else 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
