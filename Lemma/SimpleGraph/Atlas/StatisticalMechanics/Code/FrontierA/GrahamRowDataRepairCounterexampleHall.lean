import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairCounterexampleHall.Part2
open StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[weightedCollision_leaf_color_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean)
-/
@[path]
private lemma weightedCollision_leaf_color_two_eq
  {c : leftFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3} :
-- imply
  c.1 ⟨3, Finset.mem_univ 3⟩ = 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_leaf_color_two c

/--
[weightedCollisionRowDataEmbedding_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean)
-/
@[path]
private lemma weightedCollisionRowDataEmbedding_related_eq
  {d : leftRowData weightedCollisionEnds Finset.univ 1 0 2 3} :
-- imply
  RowDataRepairRelated weightedCollisionEnds Finset.univ 1 0 2 3 d (weightedCollisionRowDataEmbedding d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollisionRowDataEmbedding_related d

/--
[weightedCollision_rowDataRepairHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean)
-/
@[path]
private lemma weightedCollision_rowDataRepairHall_eq :
-- imply
  RowDataRepairHall weightedCollisionEnds Finset.univ 1 0 2 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_rowDataRepairHall

/--
[weightedCollision_weightedRowMinor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean)
-/
@[path]
private lemma weightedCollision_weightedRowMinor_eq :
-- imply
  GrahamWeightedRowMinor weightedCollisionEnds Finset.univ 1 0 2 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.weightedCollision_weightedRowMinor


-- created on 2026-10-23
