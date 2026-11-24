import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.flip_apply_same
open BooleanAnalysis Bool


/--
[flip_apply_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {x : Fin n → Bool}
  {i j : Fin n}
-- given
  (h : j ≠ i) :
-- imply
  BooleanAnalysis.flip x i j = x j := by
-- proof
  simp [BooleanAnalysis.flip, Function.update_of_ne h]


lemma BooleanAnalysis.flip_apply_ne
  {x : Fin n → Bool}
  {i j : Fin n}
-- given
  (h : j ≠ i) :
-- imply
  BooleanAnalysis.flip x i j = x j :=
-- proof
  main h


-- created on 2026-10-23
-- updated on 2026-11-24
