module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.Convolution
open Finset BigOperators BooleanFourier


public section

/--
[boolToReal_xnor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Convolution.lean)
-/
@[path]
private theorem main
  {a b : Bool} :
-- imply
  boolToReal (!(a ^^ b)) = boolToReal a * boolToReal b := by
-- proof
  cases a <;> cases b <;> simp [boolToReal]


theorem BooleanFourier.boolToReal_xnor
  {a b : Bool} :
-- imply
  boolToReal (!(a ^^ b)) = boolToReal a * boolToReal b := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
