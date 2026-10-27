import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_pos_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_pos_of_mem_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
  {omega : R.Configuration}
-- given
  (hq : 0 < q)
  (homega : omega ∈ A) :
-- imply
  0 < fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_pos_of_mem R hq A omega homega

/--
[fkRectRightBand_distinguished_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectRightBand_distinguished_reachable_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
-- given
  (hx : cut <= x.val) :
-- imply
  (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable (fkRectRightBandRowOne R cut x hx) (fkRectRightBandLastRow R cut x hx) := by
-- proof
  apply StatMech.FrontierD.fkRectRightBand_distinguished_reachable R cut x hx

/--
[fkRectRightBandConnectionProduct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectRightBandConnectionProduct_pos_eq
  {R : FKRectTorus}
  {cut : Nat}
  {q : Real}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hq : 0 < q)
  (hreaches : ∀ xy ∈ t, (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable xy.1 xy.2) :
-- imply
  0 < ∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2 := by
-- proof
  apply StatMech.FrontierD.fkRectRightBandConnectionProduct_pos R cut hq t hreaches

/--
[fkRectCriticalWindingOneMass_pos_of_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectCriticalWindingOneMass_pos_of_source_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
  (hproduct : 0 < ∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (hbarrier : 0 < fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap)) :
-- imply
  0 < fkRectCriticalWindingOneMass R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingOneMass_pos_of_source R leftRight cut hsep hleft hq hgap x hx hchosen t hspans hproduct hbarrier

/--
[windingOne_negLogRate_le_source_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma windingOne_negLogRate_le_source_cost_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
  (hproduct : 0 < ∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (hbarrier : 0 < fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap)) :
-- imply
  -Real.log (fkRectCriticalWindingOneMass R q) / R.height <= -Real.log (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) / R.height + -Real.log (fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap)) / R.height + -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
-- proof
  apply StatMech.FrontierD.windingOne_negLogRate_le_source_cost R leftRight cut hsep hleft hq hgap x hx hchosen t hspans hproduct hbarrier

/--
[FKRectWindingOneSource.connectionProduct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma connectionProduct_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {source : FKRectWindingOneSource R q}
-- given
  (hq : 0 < q) :
-- imply
  0 < source.connectionProduct := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.connectionProduct_pos source hq

/--
[FKRectWindingOneSource.connectionProduct_negLogRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma connectionProduct_negLogRate_le_eq
  {R : FKRectTorus}
  {q a : Real}
  {source : FKRectWindingOneSource R q}
-- given
  (ha : 0 < a)
  (hlower : ∀ xy ∈ source.pairs, a <= FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R source.cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  -Real.log source.connectionProduct / R.height <= (source.pairs.card : Real) * (-Real.log a) / R.height := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.connectionProduct_negLogRate_le source ha hlower

/--
[FKRectWindingOneSource.connectionProduct_negLogRate_le_of_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma connectionProduct_negLogRate_le_of_mul_pow_eq
  {R : FKRectTorus}
  {q C a : Real}
  {source : FKRectWindingOneSource R q}
  {n : Nat}
-- given
  (hC : 0 < C)
  (ha : 0 < a)
  (hlower : C * a ^ n <= source.connectionProduct) :
-- imply
  -Real.log source.connectionProduct / R.height <= ((n : Real) * (-Real.log a) + (-Real.log C)) / R.height := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.connectionProduct_negLogRate_le_of_mul_pow source n hC ha hlower

/--
[FKRectWindingOneSource.connectionProduct_negLogRate_le_of_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma connectionProduct_negLogRate_le_of_card_eq
  {R : FKRectTorus}
  {q a : Real}
  {source : FKRectWindingOneSource R q}
  {blocks : Nat}
-- given
  (hcard : source.pairs.card <= blocks)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hlower : ∀ xy ∈ source.pairs, a <= FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R source.cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  -Real.log source.connectionProduct / R.height <= (blocks : Real) * (-Real.log a) / R.height := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.connectionProduct_negLogRate_le_of_card source blocks hcard ha ha1 hlower

/--
[FKRectWindingOneSource.barrierMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma barrierMass_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {source : FKRectWindingOneSource R q}
-- given
  (hq : 0 < q) :
-- imply
  0 < source.barrierMass := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.barrierMass_pos source hq

/--
[FKRectWindingOneSource.windingOneMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma windingOneMass_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {source : FKRectWindingOneSource R q}
-- given
  (hq : 1 <= q) :
-- imply
  0 < fkRectCriticalWindingOneMass R q := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.windingOneMass_pos source hq

/--
[fkRectCriticalWindingOneMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectCriticalWindingOneMass_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 < fkRectCriticalWindingOneMass R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingOneMass_pos R hq

/--
[fkRectSourceLeftBarrier_mass_pos_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectSourceLeftBarrier_mass_pos_of_one_le_eq
  {R : FKRectTorus}
  {right : Nat}
  {q : Real}
-- given
  (hone : 1 <= right)
  (hright : right + 1 < R.width)
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R right (fkRectUnitLeftBarrierGap R)) := by
-- proof
  apply StatMech.FrontierD.fkRectSourceLeftBarrier_mass_pos_of_one_le R right hone hright hq

/--
[FKRectWindingOneSource.windingOne_negLogRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma windingOne_negLogRate_le_eq
  {R : FKRectTorus}
  {q : Real}
  {source : FKRectWindingOneSource R q}
-- given
  (hq : 1 <= q) :
-- imply
  -Real.log (fkRectCriticalWindingOneMass R q) / R.height <= -Real.log source.connectionProduct / R.height + -Real.log source.barrierMass / R.height + -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
-- proof
  apply StatMech.FrontierD.FKRectWindingOneSource.windingOne_negLogRate_le source hq

/--
[chargeOne_negLogRate_le_windingOne_add_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma chargeOne_negLogRate_le_windingOne_add_constant_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (hmass : 0 < fkRectCriticalWindingOneMass R q) :
-- imply
  -Real.log (sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / R.height <= -Real.log (fkRectCriticalWindingOneMass R q) / R.height + (Real.log (fkRectChargeOneModeCost (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2) - Real.log ((2 / Real.sqrt q) ^ 2 / q)) / R.height := by
-- proof
  apply StatMech.FrontierD.chargeOne_negLogRate_le_windingOne_add_constant R hq hmass

/--
[chargeOneRate_le_windingOneRate_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma chargeOneRate_le_windingOneRate_of_tendsto_eq
  {q chargeRate windingRate : Real}
-- given
  (R : Nat -> FKRectTorus)
  (hq : 4 < q)
  (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
  (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
  (hcharge : Tendsto (fun n => -Real.log (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1 (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (R n).height) atTop (nhds chargeRate))
  (hwind : Tendsto (fun n => -Real.log (fkRectCriticalWindingOneMass (R n) q) / (R n).height) atTop (nhds windingRate)) :
-- imply
  chargeRate <= windingRate := by
-- proof
  apply StatMech.FrontierD.chargeOneRate_le_windingOneRate_of_tendsto R hq hmass hheight hcharge hwind

/--
[le_of_tendsto_of_eventually_le_add_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma le_of_tendsto_of_eventually_le_add_vanishing_eq
  {limit upper : Real}
-- given
  (f g error : Nat -> Real)
  (hf : Tendsto f atTop (nhds limit))
  (herror : Tendsto error atTop (nhds 0))
  (hle : ∀ᶠ n in atTop, f n <= g n + error n)
  (hg : forall epsilon : Real, 0 < epsilon -> ∀ᶠ n in atTop, g n <= upper + epsilon) :
-- imply
  limit <= upper := by
-- proof
  apply StatMech.FrontierD.le_of_tendsto_of_eventually_le_add_vanishing f g error hf herror hle hg

/--
[chargeOneRate_le_of_windingOne_eventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma chargeOneRate_le_of_windingOne_eventualUpper_eq
  {q chargeRate windingUpper : Real}
-- given
  (R : Nat -> FKRectTorus)
  (hq : 4 < q)
  (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
  (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
  (hcharge : Tendsto (fun n => -Real.log (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1 (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (R n).height) atTop (nhds chargeRate))
  (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ n in atTop, -Real.log (fkRectCriticalWindingOneMass (R n) q) / (R n).height <= windingUpper + epsilon) :
-- imply
  chargeRate <= windingUpper := by
-- proof
  apply StatMech.FrontierD.chargeOneRate_le_of_windingOne_eventualUpper R hq hmass hheight hcharge hwind

/--
[fixedChargeVertical_chargeOneRate_le_windingOneRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fixedChargeVertical_chargeOneRate_le_windingOneRate_eq
  {q windingRate : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hmass : forall m, 0 < fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q)
  (hwind : Tendsto (fun m => -Real.log (fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q) / (fkRectFixedChargeVerticalFamily 1 k m).height) atTop (nhds windingRate)) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingRate := by
-- proof
  apply StatMech.FrontierD.fixedChargeVertical_chargeOneRate_le_windingOneRate hq k hmass hwind

/--
[fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_eq
  {q windingUpper : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hmass : forall m, 0 < fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q)
  (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop, -Real.log (fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q) / (fkRectFixedChargeVerticalFamily 1 k m).height <= windingUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
-- proof
  apply StatMech.FrontierD.fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper hq k hmass hwind

/--
[fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional_eq
  {q windingUpper : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop, -Real.log (fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q) / (fkRectFixedChargeVerticalFamily 1 k m).height <= windingUpper + epsilon) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
-- proof
  apply StatMech.FrontierD.fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional hq k hwind

/--
[fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hbound : forall k : Nat, -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= xiInv) :
-- imply
  fkQgt4SixVertexGapRate q <= xiInv := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds hq hbound

/--
[fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hmass : forall k m, 0 < fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q)
  (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop, -Real.log (fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q) / (fkRectFixedChargeVerticalFamily 1 k m).height <= xiInv + epsilon) :
-- imply
  fkQgt4SixVertexGapRate q <= xiInv := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper hq hmass hwind

/--
[fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_unconditional_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop, -Real.log (fkRectCriticalWindingOneMass (fkRectFixedChargeVerticalFamily 1 k m) q) / (fkRectFixedChargeVerticalFamily 1 k m).height <= xiInv + epsilon) :
-- imply
  fkQgt4SixVertexGapRate q <= xiInv := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_unconditional hq hwind

/--
[fkQgt4SixVertexGapRate_le_of_sourceCostEventualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_of_sourceCostEventualUpper_eq
  {q xiInv : Real}
  {source : forall k m, FKRectWindingOneSource (fkRectFixedChargeVerticalFamily 1 k m) q}
-- given
  (hq : 4 < q)
  (hsourceCost : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop, -Real.log (source k m).connectionProduct / (fkRectFixedChargeVerticalFamily 1 k m).height + -Real.log (source k m).barrierMass / (fkRectFixedChargeVerticalFamily 1 k m).height <= xiInv + epsilon) :
-- imply
  fkQgt4SixVertexGapRate q <= xiInv := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_of_sourceCostEventualUpper hq source hsourceCost


-- created on 2026-10-23
