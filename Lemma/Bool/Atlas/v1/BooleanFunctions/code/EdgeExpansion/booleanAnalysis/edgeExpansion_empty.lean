import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.edgeExpansion_nonneg
open BooleanAnalysis Bool


/--
[edgeExpansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {n : ℕ} :
-- imply
  edgeExpansion n (∅ : Finset (Fin n → Bool)) = 0 := by
-- proof
  simp [edgeExpansion]


lemma BooleanAnalysis.edgeExpansion_empty
  {n : ℕ} :
-- imply
  edgeExpansion n (∅ : Finset (Fin n → Bool)) = 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
