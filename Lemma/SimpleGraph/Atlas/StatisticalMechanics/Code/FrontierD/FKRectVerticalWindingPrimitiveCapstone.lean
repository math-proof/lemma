import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPrimitiveCapstone
open StatMech StatMech.FrontierD


/--
[rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent, ¬ FKRectPrimalComponentHasNet R omega K → (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
-- imply
  FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
-- proof
  apply StatMech.FrontierD.rankOnePositiveBoundaryCutFiberBound_of_card_nonzero_le_two_unconditional R omega hcard

/--
[fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcard : ∀ K : (fkRectOpenGraph R omega).ConnectedComponent, ¬ FKRectPrimalComponentHasNet R omega K → (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_card_nonzero_le_two R omega hcard

/--
[fkRectWindingTailForcesHorizontalCylinderCrossings_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma fkRectWindingTailForcesHorizontalCylinderCrossings_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {r : Nat}
-- given
  (hcard : ∀ omega K, ¬ FKRectPrimalComponentHasNet R omega K → (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2) :
-- imply
  FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
-- proof
  apply StatMech.FrontierD.fkRectWindingTailForcesHorizontalCylinderCrossings_of_card_nonzero_le_two R r hcard

/--
[rankOnePositiveBoundaryCutFiberBound_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma rankOnePositiveBoundaryCutFiberBound_unconditional_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega := by
-- proof
  apply StatMech.FrontierD.rankOnePositiveBoundaryCutFiberBound_unconditional R omega

/--
[fkRectUnorientedVerticalWindingNumber_le_horizontalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_horizontalCut_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_horizontalCut R omega

/--
[fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveCapstone.lean)
-/
@[path]
private lemma fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional_eq
  {R : FKRectTorus}
  {r : Nat} :
-- imply
  FKRectWindingTailForcesHorizontalCylinderCrossings R r := by
-- proof
  apply StatMech.FrontierD.fkRectWindingTailForcesHorizontalCylinderCrossings_unconditional R r


-- created on 2026-10-23
