import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.weightedRegularGraph.edgeExpansion_empty
open BooleanAnalysis Bool


/--
[WeightedRegularGraph.edgeExpansion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V}
  {S : Finset V} :
-- imply
  0 ≤ G.edgeExpansion S := by
-- proof
  unfold WeightedRegularGraph.edgeExpansion
  split_ifs with h
  · exact le_refl 0
  ·
    apply div_nonneg
    ·
      apply Finset.sum_nonneg
      intro x _
      apply Finset.sum_nonneg
      intro y _
      exact G.weight_nonneg x y
    ·
      apply mul_nonneg
      ·
        exact le_of_lt G.degree_pos
      ·
        exact Nat.cast_nonneg _


lemma BooleanAnalysis.WeightedRegularGraph.edgeExpansion_nonneg
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V}
  {S : Finset V} :
-- imply
  0 ≤ G.edgeExpansion S := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
