module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone.booleanFourier.flipCoord_ne_self'
open BooleanFourier Bool


public section

/--
[le_flipCoord_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n}
-- given
  (hxi : x i = false) :
-- imply
  x ≤ flipCoord x i := by
-- proof
  intro j; simp only [flipCoord, Function.update]
  split_ifs with h
  ·
    subst h
    rw [hxi]
    exact Bool.false_le _
  · exact le_refl _


theorem BooleanFourier.le_flipCoord_of_false
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n}
-- given
  (hxi : x i = false) :
-- imply
  x ≤ flipCoord x i :=
-- proof
  main hxi


-- created on 2026-10-23
-- updated on 2026-11-24
