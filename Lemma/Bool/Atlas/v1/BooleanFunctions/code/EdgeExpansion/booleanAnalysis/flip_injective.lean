import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.flip_apply_ne
open BooleanAnalysis Bool


/--
[flip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {x : Fin n → Bool} :
-- imply
  Function.Injective (BooleanAnalysis.flip x) := by
-- proof
  intro i j hij
  by_contra h_ne
  have hi : BooleanAnalysis.flip x i i = BooleanAnalysis.flip x j i := congr_fun hij i
  rw [flip_apply_same, flip_apply_ne (i := j) (j := i) h_ne] at hi
  simp at hi


lemma BooleanAnalysis.flip_injective
  {x : Fin n → Bool} :
-- imply
  Function.Injective (BooleanAnalysis.flip x) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
