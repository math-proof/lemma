module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.boolToReal_true
open Finset BigOperators BooleanFourier Bool


public section

/--
[boolToReal_false](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main :
-- imply
  boolToReal false = -1 := by
-- proof
  simp [boolToReal]


theorem BooleanFourier.boolToReal_false :
-- imply
  boolToReal false = -1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
