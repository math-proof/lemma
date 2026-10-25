import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalBarrierCapstone
open Set SimpleGraph Filter Topology StatMech StatMech.FrontierD


/--
[fkRectPositiveBandBarrierConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectPositiveBandBarrierConstant_pos_eq
  {k scale : Nat}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 < fkRectPositiveBandBarrierConstant k scale q := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBarrierConstant_pos k scale hq

/--
[fkRectPositiveBandBulkBlocks_le_four_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectPositiveBandBulkBlocks_le_four_mul_eq
  {k scale blocks : Nat}
  {q : Real}
  {B : FKRectPositiveBandOrientedBlock (fkRectWindingBlockVerticalFamily k scale blocks) q scale}
-- given
  (hscale : 6 ≤ scale) :
-- imply
  fkRectPositiveBandBulkBlocks B ≤ 4 * (blocks + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBulkBlocks_le_four_mul hscale B

/--
[FKRectPositiveBandOrientedBlock.massFloor_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma massFloor_le_one_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hq : 1 ≤ q) :
-- imply
  B.massFloor ≤ 1 := by
-- proof
  apply StatMech.FrontierD.FKRectPositiveBandOrientedBlock.massFloor_le_one hq B

/--
[fkRectDevelopedReflectedEndpointLower_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectDevelopedReflectedEndpointLower_le_one_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hq : 1 ≤ q)
  (hB : B.massFloor = fkRectDevelopedReflectedEndpointLower q scale) :
-- imply
  fkRectDevelopedReflectedEndpointLower q scale ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectedEndpointLower_le_one hq B hB

/--
[fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor_eq
  {k scale : Nat}
  {q crossingFloor : Real}
-- given
  (hscale : 6 ≤ scale)
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hq : 1 ≤ q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : ∀ᶠ blocks in atTop, crossingFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∀ᶠ blocks in atTop, fkRectPositiveBandBarrierConstant k scale q * (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) ^ (blocks + 1) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (4 * scale + 1) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks))) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossingFloor k scale hscale hwidth hq hcrossingFloor hcross

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor_eq
  {k scale : Nat}
  {q crossingFloor : Real}
-- given
  (hscale : 6 ≤ scale)
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hq : 1 ≤ q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : ∀ᶠ blocks in atTop, crossingFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (4 * scale + 1) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height ≤ -Real.log (fkRectDevelopedReflectedEndpointLowerOf crossingFloor scale ^ 4) / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossingFloor k scale hscale hwidth hq hcrossingFloor hcross

/--
[fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossing_eq
  {k scale : Nat}
  {q : Real}
-- given
  (hscale : 6 ≤ scale)
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hq : 1 ≤ q)
  (hcross : ∀ᶠ blocks in atTop, 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∀ᶠ blocks in atTop, fkRectPositiveBandBarrierConstant k scale q * (fkRectDevelopedReflectedEndpointLower q scale ^ 4) ^ (blocks + 1) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (4 * scale + 1) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks))) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_eventually_dualPullbackLower_of_horizontalCrossing k scale hscale hwidth hq hcross

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossing_eq
  {k scale : Nat}
  {q : Real}
-- given
  (hscale : 6 ≤ scale)
  (hwidth : 12 * scale + 2 < 2 * (k + 3))
  (hq : 1 ≤ q)
  (hcross : ∀ᶠ blocks in atTop, 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (4 * scale + 1) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height ≤ -Real.log (fkRectDevelopedReflectedEndpointLower q scale ^ 4) / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_horizontalCrossing k scale hscale hwidth hq hcross


-- created on 2026-10-23
