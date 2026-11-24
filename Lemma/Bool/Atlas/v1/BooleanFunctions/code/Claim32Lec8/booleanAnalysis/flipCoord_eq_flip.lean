import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim32Lec8.booleanAnalysis.indicator_ne_iff
open BooleanAnalysis Finset Bool


/--
[flipCoord_eq_flip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  BooleanFourier.flipCoord x i = BooleanAnalysis.flip x i := by
-- proof
  ext j
  if h : j = i then
    subst h
    simp [BooleanFourier.flipCoord, BooleanAnalysis.flip]
  else
    simp [BooleanFourier.flipCoord, BooleanAnalysis.flip, Function.update_of_ne h]


lemma BooleanAnalysis.flipCoord_eq_flip
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  BooleanFourier.flipCoord x i = BooleanAnalysis.flip x i := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
