module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.le_flipCoord_of_false
open BooleanFourier Bool


public section

/--
[flipCoord_le_of_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n}
-- given
  (hxi : x i = true) :
-- imply
  flipCoord x i ≤ x := by
-- proof
  intro j; simp only [flipCoord, Function.update]
  split_ifs with h
  ·
    subst h
    rw [hxi]
    exact Bool.false_le _
  · exact le_refl _


theorem BooleanFourier.flipCoord_le_of_true
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n}
-- given
  (hxi : x i = true) :
-- imply
  flipCoord x i ≤ x :=
-- proof
  main hxi


-- created on 2026-10-23
-- updated on 2026-11-24
