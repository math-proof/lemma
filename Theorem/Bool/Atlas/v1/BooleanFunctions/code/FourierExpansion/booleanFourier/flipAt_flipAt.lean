module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.chi_ne_zero
open Finset BigOperators BooleanFourier Bool


public section

/--
[flipAt_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j (flipAt j x) = x := by
-- proof
  ext i
  simp only [flipAt, Function.update]
  split_ifs with h
  ·
    subst h
    simp
  · rfl


theorem BooleanFourier.flipAt_flipAt
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j (flipAt j x) = x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
