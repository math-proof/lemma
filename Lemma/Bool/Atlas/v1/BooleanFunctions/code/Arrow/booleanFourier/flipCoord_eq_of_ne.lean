import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.arrow_viable_implies_unique_pivot
open BooleanFourier Bool


/--
[flipCoord_eq_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {z : Fin n → Bool}
  {a : Fin n}
  {b : Bool}
-- given
  (h : ¬(z a = b)) :
-- imply
  (flipCoord z a) a = b := by
-- proof
  simp only [flipCoord, Function.update_self]
  cases hza : z a <;> cases hb : b
  · exact absurd rfl (hza ▸ hb ▸ h)
  · rfl
  · rfl
  · exact absurd rfl (hza ▸ hb ▸ h)


lemma BooleanFourier.flipCoord_eq_of_ne
  {n : ℕ}
  {z : Fin n → Bool}
  {a : Fin n}
  {b : Bool}
-- given
  (h : ¬(z a = b)) :
-- imply
  (flipCoord z a) a = b :=
-- proof
  main h


-- created on 2026-10-23
-- updated on 2026-11-24
