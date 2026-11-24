import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceDerivative.booleanFourier.boolDiscreteDerivative_apply
open BooleanFourier Bool


/--
[flipCoord_insertNth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  flipCoord (Fin.insertNth i b y) i = Fin.insertNth i (!b) y := by
-- proof
  simp only [flipCoord, Fin.insertNth_apply_same]
  rw [Fin.update_insertNth]


lemma BooleanFourier.flipCoord_insertNth
  {n : ℕ}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  flipCoord (Fin.insertNth i b y) i = Fin.insertNth i (!b) y := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
