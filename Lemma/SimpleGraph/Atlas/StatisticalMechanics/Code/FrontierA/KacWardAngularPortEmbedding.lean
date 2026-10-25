import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
open StatMech StatMech.FrontierA


/--
[KWStraightLineEmbedding.exists_angularPortSplitEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortEmbedding.lean)
-/
@[path]
private lemma exists_angularPortSplitEmbedding_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  Nonempty (KWStraightLineEmbedding (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.exists_angularPortSplitEmbedding embedding


-- created on 2026-10-23
