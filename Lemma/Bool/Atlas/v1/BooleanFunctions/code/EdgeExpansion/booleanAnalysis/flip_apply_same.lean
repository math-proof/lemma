import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.weightedRegularGraph.edgeExpansion_nonneg
open BooleanAnalysis Bool


/--
[flip_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  BooleanAnalysis.flip x i i = !x i := by
-- proof
  simp [BooleanAnalysis.flip]


lemma BooleanAnalysis.flip_apply_same
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  BooleanAnalysis.flip x i i = !x i := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
