module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.chi_singleton
open BooleanFourier Bool


public section

/--
[flipCoord_flipCoord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord (flipCoord x i) i = x := by
-- proof
  ext j; simp only [flipCoord, Function.update]; split_ifs with h
  ·
    subst h
    simp
  · rfl


theorem BooleanFourier.flipCoord_flipCoord
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord (flipCoord x i) i = x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
