import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceDerivative.booleanFourier.flipCoord_insertNth
open BooleanFourier Bool


/--
[ne_flipCoord_iff_insertNth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  (f (Fin.insertNth i b y) ≠ f (flipCoord (Fin.insertNth i b y) i)) ↔ (f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)) := by
-- proof
  rw [flipCoord_insertNth]
  cases b
  · exact ne_comm
  · rfl


lemma BooleanFourier.ne_flipCoord_iff_insertNth
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  (f (Fin.insertNth i b y) ≠ f (flipCoord (Fin.insertNth i b y) i)) ↔ (f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
