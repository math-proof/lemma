import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalBarrierAssembly
open Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierAssembly.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossingFloor_eq
  {q crossingFloor : Real}
-- given
  (hq : 4 < q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : forall scale k : Nat, 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, crossingFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossingFloor hq hcrossingFloor hcross

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierAssembly.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor_eq
  {q crossingFloor : Real}
-- given
  (hq : 4 < q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : forall scale k : Nat, Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, crossingFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenHorizontalCrossingFloor hq hcrossingFloor hcross

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierAssembly.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hcross : forall scale k : Nat, 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, 1 / (2 * (1 + q)) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_horizontalCrossing hq hcross


-- created on 2026-10-23
