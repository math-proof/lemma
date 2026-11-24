module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.flipAt_flipAt
open Finset BigOperators BooleanFourier Bool


public section

/--
[flipAt_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j x ≠ x := by
-- proof
  intro h
  have := congr_fun h j
  simp [flipAt, Function.update_self] at this


theorem BooleanFourier.flipAt_ne_self
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j x ≠ x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
