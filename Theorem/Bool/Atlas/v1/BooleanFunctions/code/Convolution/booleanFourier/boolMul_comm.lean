module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Convolution.booleanFourier.chi_boolMul
open Finset BigOperators BooleanFourier Bool


public section

/--
[boolMul_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Convolution.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  boolMul x y = boolMul y x := by
-- proof
  ext i
  simp [boolMul, Bool.xor_comm]


theorem BooleanFourier.boolMul_comm
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  boolMul x y = boolMul y x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
