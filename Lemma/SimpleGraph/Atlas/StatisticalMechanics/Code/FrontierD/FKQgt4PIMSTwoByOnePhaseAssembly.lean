import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[fkRectDevelopedRectangleHorizontalCrossingEvent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkRectDevelopedRectangleHorizontalCrossingEvent_zero_eq
  {R : FKRectTorus} :
-- imply
  fkRectDevelopedRectangleHorizontalCrossingEvent R 0 0 0 0 0 = Set.univ := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedRectangleHorizontalCrossingEvent_zero R

/--
[fkRectCritical_developedHorizontalCrossingMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkRectCritical_developedHorizontalCrossingMass_zero_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R 0 0 0 0 0) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedHorizontalCrossingMass_zero R hq

/--
[fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 1 <= q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  forall scale k : Nat, Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor ^ 2 / (1 + q) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_evenThreeByOneCrossingFloor_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hfixed : forall r : Nat, 2 <= r -> ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge hq hhard hcross hfixed

/--
[fkQgt4_phase_conclusions_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_phase_conclusions_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4_phase_conclusions_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding hq hhard hcross hwind

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hfixed : forall r : Nat, 2 <= r -> ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_fixedCharge hq hhard hcross hfixed

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_windingTailLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_windingTailLimits_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (windingRate normalizationRate : Nat -> Nat -> Real)
  (hwindVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k m) q r) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (windingRate r k)))
  (hwindHorizontal : forall r : Nat, 2 <= r -> Tendsto (windingRate r) atTop (nhds (((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2))))
  (hnormalizationVertical : forall r : Nat, 2 <= r -> forall k : Nat, Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (normalizationRate r k)))
  (hnormalizationHorizontal : forall r : Nat, 2 <= r -> Tendsto (normalizationRate r) atTop (nhds 0)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_windingTailLimits hq hhard hcross windingRate normalizationRate hwindVertical hwindHorizontal hnormalizationVertical hnormalizationHorizontal

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_uniformDiagonalLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_uniformDiagonalLimits_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hwind : forall r : Nat, 2 <= r -> forall m : Nat -> Nat, (forall k, k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2))))
  (hnormalization : forall r : Nat, 2 <= r -> forall m : Nat -> Nat, (forall k, k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_uniformDiagonalLimits hq hhard hcross hwind hnormalization

/--
[fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
  {hardFloor : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_potts_phases_of_evenTwoByOneCrossingFloor q hq J hJ hhard hcross

/--
[fkQgt4_critical_ergodic_potts_phases_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PIMSTwoByOnePhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_ergodic_potts_phases_of_evenTwoByOneCrossingFloor_eq
  {q : Nat}
  [NeZero q]
  {hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_ergodic_potts_phases_of_evenTwoByOneCrossingFloor q hq hhard hcross


-- created on 2026-10-23
