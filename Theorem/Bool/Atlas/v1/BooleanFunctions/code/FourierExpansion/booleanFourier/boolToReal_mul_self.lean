module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.boolToReal_ne_zero
open Finset BigOperators BooleanFourier Bool


public section

/--
[boolToReal_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {b : Bool} :
-- imply
  boolToReal b * boolToReal b = 1 := by
-- proof
  cases b <;> simp [boolToReal]


theorem BooleanFourier.boolToReal_mul_self
  {b : Bool} :
-- imply
  boolToReal b * boolToReal b = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
