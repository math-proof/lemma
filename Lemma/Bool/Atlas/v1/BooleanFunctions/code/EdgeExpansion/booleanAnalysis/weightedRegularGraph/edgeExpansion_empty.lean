import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.EdgeExpansion
open BooleanAnalysis


/--
[WeightedRegularGraph.edgeExpansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V} :
-- imply
  G.edgeExpansion ∅ = 0 := by
-- proof
  simp [WeightedRegularGraph.edgeExpansion]


lemma BooleanAnalysis.WeightedRegularGraph.edgeExpansion_empty
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V} :
-- imply
  G.edgeExpansion ∅ = 0 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
