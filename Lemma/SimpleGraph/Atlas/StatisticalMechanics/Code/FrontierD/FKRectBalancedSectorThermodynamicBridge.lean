import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[le_negLog_div_of_le_exp_neg_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma le_negLog_div_of_le_exp_neg_mul_eq
  {mass height rate : Real}
-- given
  (hmass : 0 < mass)
  (hheight : 0 < height)
  (hupper : mass <= Real.exp (-rate * height)) :
-- imply
  rate <= -Real.log mass / height := by
-- proof
  apply StatMech.FrontierD.le_negLog_div_of_le_exp_neg_mul hmass hheight hupper

/--
[fkRectFixedChargeVerticalFamily_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_width_eq
  {r k m : Nat} :
-- imply
  (fkRectFixedChargeVerticalFamily r k m).width = 2 * (r + k + 2) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_width r k m

/--
[fkRectFixedChargeVerticalFamily_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_height_eq
  {r k m : Nat} :
-- imply
  (fkRectFixedChargeVerticalFamily r k m).height = 2 * (m + 2) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_height r k m

/--
[fkRectFixedChargeVerticalFamily_medialWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_medialWidth_eq
  {r k m : Nat} :
-- imply
  (fkRectFixedChargeVerticalFamily r k m).medialTorus.width = sixVertexFourWidth r (k + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_medialWidth r k m

/--
[fkRectFixedChargeVerticalFamily_medialHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_medialHeight_eq
  {r k m : Nat} :
-- imply
  (fkRectFixedChargeVerticalFamily r k m).medialTorus.height = 2 * (m + 2) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_medialHeight r k m

/--
[fkRectFixedChargeVerticalFamily_charge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_charge_le_eq
  {r k m : Nat} :
-- imply
  r ≤ (fkRectFixedChargeVerticalFamily r k m).medialTorus.width / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_charge_le r k m

/--
[tendsto_fkRectFixedChargeVerticalFamily_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma tendsto_fkRectFixedChargeVerticalFamily_height_eq :
-- imply
  Tendsto (fun m => (fkRectFixedChargeVerticalFamily 0 0 m).height) atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectFixedChargeVerticalFamily_height

/--
[exists_nat_diagonal_tendsto_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma exists_nat_diagonal_tendsto_above_eq
  {L : Real}
-- given
  (f : Nat -> Nat -> Real)
  (a : Nat -> Real)
  (lower : Nat -> Nat)
  (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
  (hhorizontal : Tendsto a atTop (nhds L)) :
-- imply
  exists m : Nat -> Nat, (forall k, lower k <= m k) /\ Tendsto (fun k => f k (m k)) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierD.exists_nat_diagonal_tendsto_above f a lower hvertical hhorizontal

/--
[exists_nat_diagonal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma exists_nat_diagonal_tendsto_eq
  {L : Real}
-- given
  (f : Nat -> Nat -> Real)
  (a : Nat -> Real)
  (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
  (hhorizontal : Tendsto a atTop (nhds L)) :
-- imply
  exists m : Nat -> Nat, (forall k, k <= m k) /\ Tendsto (fun k => f k (m k)) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierD.exists_nat_diagonal_tendsto f a hvertical hhorizontal

/--
[fkRectFixedCharge_vertical_negLogRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkRectFixedCharge_vertical_negLogRatio_tendsto_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun m => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k m).medialTorus r (fkRectFixedChargeVerticalFamily_charge_le r k m) c / sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k m).medialTorus 0 (Nat.zero_le _) c) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (-sixVertexFixedChargeLogRatio c r (k + 1))) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedCharge_vertical_negLogRatio_tendsto hc r k

/--
[tendsto_sixVertexFixedCharge_negLogRatio_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedCharge_negLogRatio_gap_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (hr : 1 ≤ r) :
-- imply
  Tendsto (fun k => -sixVertexFixedChargeLogRatio c r (k + 1)) atTop (nhds ((r : Real) * sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedCharge_negLogRatio_gap hc r hr

/--
[tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 1 ≤ r) :
-- imply
  Tendsto (fun k => -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) r (k + 1)) atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq r hr

/--
[exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 1 <= r)
  (lower : Nat -> Nat) :
-- imply
  exists m : Nat -> Nat, (forall k, lower k <= m k) /\ Tendsto (fun k => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r (fkRectFixedChargeVerticalFamily_charge_le r k (m k)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) := by
-- proof
  apply StatMech.FrontierD.exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_above hq r hr lower

/--
[exists_fkQgt4_fixedCharge_diagonal_tendsto_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma exists_fkQgt4_fixedCharge_diagonal_tendsto_gap_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 1 <= r) :
-- imply
  exists m : Nat -> Nat, (forall k, k <= m k) /\ Tendsto (fun k => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r (fkRectFixedChargeVerticalFamily_charge_le r k (m k)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)) := by
-- proof
  apply StatMech.FrontierD.exists_fkQgt4_fixedCharge_diagonal_tendsto_gap hq r hr

/--
[fkQgt4_fixedCharge_bound_of_diagonalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_diagonalLimits_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (m : Nat -> Nat)
  (hwind : Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hcharge : Tendsto (fun k => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r (fkRectFixedChargeVerticalFamily_charge_le r k (m k)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)))
  (hnormalization : Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_diagonalLimits hq r m hwind hcharge hnormalization

/--
[fkQgt4_fixedCharge_bound_of_diagonalWindingLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_diagonalWindingLowerBound_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (m : Nat -> Nat)
  (windingLower : Nat -> Real)
  (hwindLower : Tendsto windingLower atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hwindBound : ∀ᶠ k in atTop, windingLower k <= -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height)
  (hcharge : Tendsto (fun k => -Real.log (sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus r (fkRectFixedChargeVerticalFamily_charge_le r k (m k)) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (fkRectFixedChargeVerticalFamily r k (m k)).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds ((r : Real) * fkQgt4SixVertexGapRate q)))
  (hnormalization : Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_diagonalWindingLowerBound hq r m windingLower hwindLower hwindBound hcharge hnormalization

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hnormalization : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove hq r hr heightLower hwind hnormalization

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hnoLoop : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hfourCopy : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => fkRectFourCopyShareCost (fkRectFixedChargeVerticalFamily r k (m k)) q / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_fourCopy hq r hr heightLower hwind hnoLoop hfourCopy

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_zeroTurnTail_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_zeroTurnTail_fourCopy_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (threshold : (Nat -> Nat) -> Nat -> Nat)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (htail : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> forall k, fkRectCriticalZeroTurnAboveMass (fkRectFixedChargeVerticalFamily r k (m k)) q (threshold m k) <= (1 : Real) / 2)
  (hthreshold : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => ((threshold m k : Nat) : Real) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hheight : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop atTop)
  (hfourCopy : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => fkRectFourCopyShareCost (fkRectFixedChargeVerticalFamily r k (m k)) q / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_zeroTurnTail_fourCopy hq r hr heightLower threshold hwind htail hthreshold hheight hfourCopy

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalLimits_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (hwind : forall m : Nat -> Nat, (forall k, k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hnormalization : forall m : Nat -> Nat, (forall k, k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalLimits hq r hr hwind hnormalization

/--
[fkQgt4_fixedCharge_bound_of_windingTail_iteratedLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorThermodynamicBridge.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_windingTail_iteratedLimits_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (windingRate : Nat -> Real)
  (normalizationRate : Nat -> Real)
  (hwindVertical : forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate k)))
  (hwindHorizontal : Tendsto windingRate atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hnormalizationVertical : forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate k)))
  (hnormalizationHorizontal : Tendsto normalizationRate atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_windingTail_iteratedLimits hq r hr windingRate normalizationRate hwindVertical hwindHorizontal hnormalizationVertical hnormalizationHorizontal


-- created on 2026-10-23
