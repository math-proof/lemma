module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.flipCoord_flipCoord
open BooleanFourier Bool


public section

/--
[flipCoord_ne_self'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord x i ≠ x := by
-- proof
  intro h; have := congr_fun h i; simp [flipCoord] at this

theorem BooleanFourier.flipCoord_ne_self'
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord x i ≠ x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
