import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
open Filter MeasureTheory Topology StatMech StatMech.FrontierD


/--
[fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical_eq
  {q normalizationRate : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (hnormalization : Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds normalizationRate)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) r (k + 1) + normalizationRate := by
-- proof
  apply StatMech.FrontierD.fkQgt4_pred_exactDiagonalHalf_le_fixedChargeRate_of_normalizationVertical hq r hr k hnormalization

/--
[fkQgt4_fixedCharge_bound_of_normalizationVertical_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_normalizationVertical_unconditional_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (hnormalization : forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_normalizationVertical_unconditional hq r hr hnormalization

/--
[fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (normalizationRate : Nat -> Real)
  (hnormalizationVertical : forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate k)))
  (hnormalizationHorizontal : Tendsto normalizationRate atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_normalizationLimits_unconditional hq r hr normalizationRate hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_fixedCharge_bound_of_verticalWindingTailLimits_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_verticalWindingTailLimits_unconditional_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (windingRate normalizationRate : Nat -> Real)
  (hwindVertical : forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate k)))
  (hnormalizationVertical : forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate k)))
  (hnormalizationHorizontal : Tendsto normalizationRate atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_verticalWindingTailLimits_unconditional hq r hr windingRate normalizationRate hwindVertical hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (windingRate normalizationRate : Nat -> Nat -> Real)
  (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate r k)))
  (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate r k)))
  (hnormalizationHorizontal : forall r : Nat, 2 <= r -> Tendsto (normalizationRate r) atTop (nhds 0)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_verticalLimits hq hhard hcross windingRate normalizationRate hwindVertical hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationVertical_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hnormalization : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds 0)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationVertical hq hhard hcross hnormalization

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationLimits_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (normalizationRate : Nat -> Nat -> Real)
  (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate r k)))
  (hnormalizationHorizontal : forall r : Nat, 2 <= r -> Tendsto (normalizationRate r) atTop (nhds 0)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_normalizationLimits hq hhard hcross normalizationRate hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_verticalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_verticalLimits_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (windingRate normalizationRate : Nat -> Nat -> Real)
  (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate r k)))
  (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate r k)))
  (hnormalizationHorizontal : forall r : Nat, 2 <= r -> Tendsto (normalizationRate r) atTop (nhds 0)) :
-- imply
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : MeasureTheory.ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_verticalLimits hq hhard hcross windingRate normalizationRate hwindVertical hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_normalizationVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_normalizationVertical_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hnormalization : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds 0)) :
-- imply
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_normalizationVertical hq hhard hcross hnormalization

/--
[fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor_and_verticalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceRateCapstone.lean)
-/
@[path]
private lemma fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor_and_verticalLimits_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
  {hardFloor : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (windingRate normalizationRate : Nat -> Nat -> Real)
  (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate r k)))
  (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate r k)))
  (hnormalizationHorizontal : forall r : Nat, 2 <= r -> Tendsto (normalizationRate r) atTop (nhds 0)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (forall b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor_and_verticalLimits q hq J hJ hhard hcross windingRate normalizationRate hwindVertical hnormalizationVertical hnormalizationHorizontal


-- created on 2026-10-23
