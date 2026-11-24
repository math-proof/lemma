module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.boolToReal_sq
open Finset BigOperators BooleanFourier Bool


public section

/--
[boolToReal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {b : Bool} :
-- imply
  boolToReal b ≠ 0 := by
-- proof
  cases b <;> simp [boolToReal]


theorem BooleanFourier.boolToReal_ne_zero
  {b : Bool} :
-- imply
  boolToReal b ≠ 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
