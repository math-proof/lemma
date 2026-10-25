import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierCapstone
open Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierCapstone.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (leftRight : Nat -> Nat)
  (hone : forall scale, 1 <= leftRight scale)
  (a : Nat -> Real)
  (ha : forall scale, 0 < a scale)
  (haRate : Tendsto (fun scale => -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
  (C : Nat -> Nat -> Real)
  (hC : forall scale k, 0 < C scale k)
  (hpullback : forall scale, ∀ᶠ k in atTop, forall blocks, C scale k * a scale ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (leftRight scale) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackMulBounds hq leftRight hone a ha haRate C hC hpullback

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierCapstone.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackBounds_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (leftRight : Nat -> Nat)
  (hone : forall scale, 1 <= leftRight scale)
  (a : Nat -> Real)
  (ha : forall scale, 0 < a scale)
  (haRate : Tendsto (fun scale => -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
  (hpullback : forall scale, ∀ᶠ k in atTop, forall blocks, a scale ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (leftRight scale) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualPullbackBounds hq leftRight hone a ha haRate hpullback

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliaryMul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierCapstone.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliaryMul_eq
  {q : Real}
  {A : forall scale k blocks, Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration}
-- given
  (hq : 4 < q)
  (leftRight : Nat -> Nat)
  (hone : forall scale, 1 <= leftRight scale)
  (a : Nat -> Real)
  (ha : forall scale, 0 < a scale)
  (haRate : Tendsto (fun scale => -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
  (D : Nat -> Nat -> Real)
  (hD : forall scale k, 0 < D scale k)
  (haux : forall scale, ∀ᶠ k in atTop, forall blocks, D scale k * a scale ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (A scale k blocks))
  (hforce : forall scale, ∀ᶠ k in atTop, forall blocks, ∀ omega ∈ A scale k blocks, fkRectForceIndexedPattern (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectDualPullbackIndexSet (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectHorizontalCutEdges (fkRectWindingBlockVerticalFamily k scale blocks))) (fkRectDualPullbackConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectAllButOneOpenConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) omega ∈ fkRectDualPreimageEvent (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectNoLeftStripCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) (leftRight scale))) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliaryMul hq leftRight hone a ha haRate A D hD haux hforce

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierCapstone.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliary_eq
  {q : Real}
  {A : forall scale k blocks, Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration}
-- given
  (hq : 4 < q)
  (leftRight : Nat -> Nat)
  (hone : forall scale, 1 <= leftRight scale)
  (a : Nat -> Real)
  (ha : forall scale, 0 < a scale)
  (haRate : Tendsto (fun scale => -Real.log (a scale) / (2 * (scale + 1) : Real)) atTop (nhds 0))
  (haux : forall scale, ∀ᶠ k in atTop, forall blocks, a scale ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (A scale k blocks))
  (hforce : forall scale, ∀ᶠ k in atTop, forall blocks, ∀ omega ∈ A scale k blocks, fkRectForceIndexedPattern (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectDualPullbackIndexSet (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectHorizontalCutEdges (fkRectWindingBlockVerticalFamily k scale blocks))) (fkRectDualPullbackConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectAllButOneOpenConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) omega ∈ fkRectDualPreimageEvent (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectNoLeftStripCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) (leftRight scale))) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_dualAuxiliary hq leftRight hone a ha haRate A haux hforce


-- created on 2026-10-23
