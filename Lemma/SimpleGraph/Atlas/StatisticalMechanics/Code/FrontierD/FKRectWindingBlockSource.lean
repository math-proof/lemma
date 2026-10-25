import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
open StatMech StatMech.FrontierD


/--
[fkRectWindingBlockVerticalFamily_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockVerticalFamily_width_eq
  {k scale blocks : Nat} :
-- imply
  (fkRectWindingBlockVerticalFamily k scale blocks).width = 2 * (k + 3) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockVerticalFamily_width k scale blocks

/--
[fkRectWindingBlockVerticalFamily_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockVerticalFamily_height_eq
  {k scale blocks : Nat} :
-- imply
  (fkRectWindingBlockVerticalFamily k scale blocks).height = 2 * (scale + 1) * (blocks + 1) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockVerticalFamily_height k scale blocks

/--
[fkRectWindingBlockVerticalFamily_medialWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockVerticalFamily_medialWidth_eq
  {k scale blocks : Nat} :
-- imply
  (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.width = sixVertexFourWidth 1 (k + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockVerticalFamily_medialWidth k scale blocks

/--
[fkRectWindingBlockVerticalFamily_medialHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockVerticalFamily_medialHeight_eq
  {k scale blocks : Nat} :
-- imply
  (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.height = 2 * (scale + 1) * (blocks + 1) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockVerticalFamily_medialHeight k scale blocks

/--
[fkRectWindingBlockPathVertex_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPathVertex_first_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hx : cut <= x.val) :
-- imply
  fkRectWindingBlockPathVertex k scale blocks cut x hx 0 = fkRectRightBandRowOne (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPathVertex_first k scale blocks cut x hx

/--
[fkRectWindingBlockPathVertex_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPathVertex_last_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hx : cut <= x.val) :
-- imply
  fkRectWindingBlockPathVertex k scale blocks cut x hx (Fin.last (blocks + 1)) = fkRectRightBandLastRow (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPathVertex_last k scale blocks cut x hx

/--
[fkRectWindingBlockPathPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPathPairs_card_le_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hx : cut <= x.val) :
-- imply
  (connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card <= blocks + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPathPairs_card_le k scale blocks cut x hx

/--
[fkRectWindingBlockPath_pairMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPath_pairMap_injective_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hx : cut <= x.val) :
-- imply
  Function.Injective (fun i : Fin (blocks + 1) => (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc, fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPath_pairMap_injective k scale blocks cut x hx

/--
[fkRectWindingBlockPathPairs_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPathPairs_card_eq_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hx : cut <= x.val) :
-- imply
  (connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card = blocks + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPathPairs_card_eq k scale blocks cut x hx

/--
[mem_fkRectWindingBlockPathPairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma mem_fkRectWindingBlockPathPairs_iff_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {xy : FKRectRightStripBandVertex (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) × FKRectRightStripBandVertex (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)}
-- given
  (hx : cut <= x.val) :
-- imply
  xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx) ↔ ∃ i : Fin (blocks + 1), (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc, fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) = xy := by
-- proof
  apply StatMech.FrontierD.mem_fkRectWindingBlockPathPairs_iff k scale blocks cut x hx xy

/--
[fkRectWindingBlockPathVertex_squarePoint_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockPathVertex_squarePoint_step_eq
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {i : Fin (blocks + 1)}
-- given
  (hx : cut <= x.val) :
-- imply
  fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ).1 - fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1 = (((scale + 1 : Nat) : Int), -((scale + 1 : Nat) : Int)) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockPathVertex_squarePoint_step k scale blocks cut x hx i

/--
[fkRectWindingBlockSource_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockSource_pairs_eq
  {k scale blocks leftRight cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {q a : Real}
-- given
  (hone : 1 <= leftRight)
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < (fkRectWindingBlockVerticalFamily k scale blocks).width)
  (hx : cut <= x.val)
  (ha : 0 < a)
  (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  (fkRectWindingBlockSource k scale blocks leftRight cut hone hsep hleft x hx q a ha hlower).pairs = connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockSource_pairs k scale blocks leftRight cut hone hsep hleft x hx q a ha hlower

/--
[fkRectWindingBlockSource_connectionProduct_negLogRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockSource_connectionProduct_negLogRate_le_eq
  {k scale blocks leftRight cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {q a : Real}
-- given
  (hone : 1 <= leftRight)
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < (fkRectWindingBlockVerticalFamily k scale blocks).width)
  (hx : cut <= x.val)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  -Real.log (fkRectWindingBlockSource k scale blocks leftRight cut hone hsep hleft x hx q a ha hlower).connectionProduct / (fkRectWindingBlockVerticalFamily k scale blocks).height <= ((blocks + 1 : Nat) : Real) * (-Real.log a) / (fkRectWindingBlockVerticalFamily k scale blocks).height := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockSource_connectionProduct_negLogRate_le k scale blocks leftRight cut hone hsep hleft x hx ha ha1 hlower

/--
[fkRectWindingBlockSource_windingOne_negLogRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlockSource_windingOne_negLogRate_le_eq
  {k scale blocks leftRight cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {q a : Real}
-- given
  (hone : 1 <= leftRight)
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < (fkRectWindingBlockVerticalFamily k scale blocks).width)
  (hx : cut <= x.val)
  (hq : 1 <= q)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hlower : ∀ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  -Real.log (fkRectCriticalWindingOneMass (fkRectWindingBlockVerticalFamily k scale blocks) q) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= ((blocks + 1 : Nat) : Real) * (-Real.log a) / (fkRectWindingBlockVerticalFamily k scale blocks).height + -Real.log (fkRectWindingBlockSource k scale blocks leftRight cut hone hsep hleft x hx q a ha hlower).barrierMass / (fkRectWindingBlockVerticalFamily k scale blocks).height + -Real.log (FK.cFE (fkRectCriticalP q) q) / (fkRectWindingBlockVerticalFamily k scale blocks).height := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockSource_windingOne_negLogRate_le k scale blocks leftRight cut hone hsep hleft x hx hq ha ha1 hlower

/--
[tendsto_fkRectWindingBlockVerticalFamily_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma tendsto_fkRectWindingBlockVerticalFamily_height_eq
  {k scale : Nat} :
-- imply
  Tendsto (fun blocks => (fkRectWindingBlockVerticalFamily k scale blocks).height) atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectWindingBlockVerticalFamily_height k scale

/--
[fkRectWindingBlock_count_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_count_div_height_tendsto_eq
  {k scale : Nat} :
-- imply
  Tendsto (fun blocks : Nat => ((blocks + 1 : Nat) : Real) / (fkRectWindingBlockVerticalFamily k scale blocks).height) atTop (nhds (1 / (2 * (scale + 1) : Real))) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_count_div_height_tendsto k scale

/--
[fkRectWindingBlock_vertical_negLogRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_vertical_negLogRatio_tendsto_eq
  {c : Real}
  {k scale : Nat}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun blocks => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus 1 (by rw [fkRectWindingBlockVerticalFamily_medialWidth] exact sixVertexFourWidth_charge_le 1 (k + 1)) c / sixVertexTorusFixedChargePartitionSum (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus 0 (Nat.zero_le _) c) / (fkRectWindingBlockVerticalFamily k scale blocks).height) atTop (nhds (-sixVertexFixedChargeLogRatio c 1 (k + 1))) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_vertical_negLogRatio_tendsto hc k scale

/--
[fkRectWindingBlock_chargeOneRate_le_windingOneEventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_chargeOneRate_le_windingOneEventualUpper_eq
  {q windingUpper : Real}
  {k scale : Nat}
-- given
  (hq : 4 < q)
  (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalWindingOneMass (fkRectWindingBlockVerticalFamily k scale blocks) q) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= windingUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_chargeOneRate_le_windingOneEventualUpper hq k scale hwind

/--
[fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper_eq
  {q sourceUpper : Real}
  {k scale : Nat}
  {source : forall blocks, FKRectWindingOneSource (fkRectWindingBlockVerticalFamily k scale blocks) q}
-- given
  (hq : 4 < q)
  (hsourceCost : forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (source blocks).connectionProduct / (fkRectWindingBlockVerticalFamily k scale blocks).height + -Real.log (source blocks).barrierMass / (fkRectWindingBlockVerticalFamily k scale blocks).height <= sourceUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= sourceUpper := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_chargeOneRate_le_sourceCostEventualUpper hq k scale source hsourceCost

/--
[fkRectWindingBlock_chargeOneRate_le_productPowAndBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_chargeOneRate_le_productPowAndBarrier_eq
  {q a C barrierUpper : Real}
  {k scale : Nat}
  {source : forall blocks, FKRectWindingOneSource (fkRectWindingBlockVerticalFamily k scale blocks) q}
-- given
  (hq : 4 < q)
  (ha : 0 < a)
  (hC : 0 < C)
  (hproduct : forall blocks, C * a ^ (blocks + 1) <= (source blocks).connectionProduct)
  (hbarrier : forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (source blocks).barrierMass / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log a / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_chargeOneRate_le_productPowAndBarrier hq ha hC k scale source hproduct hbarrier

/--
[fkRectWindingBlock_chargeOneRate_le_blockAndBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkRectWindingBlock_chargeOneRate_le_blockAndBarrier_eq
  {q a barrierUpper : Real}
  {k scale leftRight cut : Nat}
  {x : Fin (2 * (k + 3))}
-- given
  (hq : 4 < q)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hone : 1 <= leftRight)
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hx : cut <= x.val)
  (hblock : forall blocks, ∀ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (hbarrier : forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log a / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_chargeOneRate_le_blockAndBarrier hq ha ha1 k scale leftRight cut hone hsep hleft x hx hblock hbarrier

/--
[fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds_eq
  {q upper : Real}
-- given
  (hq : 4 < q)
  (hbound : ∀ᶠ k in atTop, -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= upper) :
-- imply
  fkQgt4SixVertexGapRate q <= upper := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_of_eventualChargeOneVerticalBounds hq hbound

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (barrierUpper : Nat -> Real)
  (hbarrier : Tendsto barrierUpper atTop (nhds 0))
  (hscale : forall scale, fkQgt4SixVertexGapRate q <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) / (2 * (scale + 1) : Real) + barrierUpper scale) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_scaleBounds hq barrierUpper hbarrier hscale

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_blockBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_blockBounds_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (barrierUpper : Nat -> Real)
  (hbarrier : Tendsto barrierUpper atTop (nhds 0))
  (hcharge : forall scale, ∀ᶠ k in atTop, -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) / (2 * (scale + 1) : Real) + barrierUpper scale) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_blockBounds hq barrierUpper hbarrier hcharge


-- created on 2026-10-23
