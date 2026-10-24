import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingRankOneReduction
open StatMech StatMech.FrontierD


/--
[fkRectPositiveVerticalBoundaryCutFiberBound_of_rankOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingRankOneReduction.lean)
-/
@[path]
private lemma fkRectPositiveVerticalBoundaryCutFiberBound_of_rankOne_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (h : FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
-- imply
  FKRectPositiveVerticalBoundaryCutFiberBound R omega := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveVerticalBoundaryCutFiberBound_of_rankOne R omega h

/--
[fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingRankOneReduction.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (h : FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_rankOne R omega h

/--
[fkRectWindingTailForcesHorizontalCylinderCrossings_of_rankOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingRankOneReduction.lean)
-/
@[path]
private lemma fkRectWindingTailForcesHorizontalCylinderCrossings_of_rankOne_eq
  {R : FKRectTorus}
  {r : Nat}
-- given
  (h : ∀ omega, FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega) :
-- imply
  FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
-- proof
  apply StatMech.FrontierD.fkRectWindingTailForcesHorizontalCylinderCrossings_of_rankOne R r h


-- created on 2026-10-23
