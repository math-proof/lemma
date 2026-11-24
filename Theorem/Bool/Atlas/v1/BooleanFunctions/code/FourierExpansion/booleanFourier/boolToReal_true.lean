module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
open Finset BigOperators BooleanFourier


public section

/--
[boolToReal_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main :
-- imply
  boolToReal true = 1 := by
-- proof
  simp [boolToReal]


theorem BooleanFourier.boolToReal_true :
-- imply
  boolToReal true = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
