import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule
open Filter Topology MeasureTheory StatMech StatMech.FrontierD


/--
[exists_nat_uniform_lower_tendsto_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma exists_nat_uniform_lower_tendsto_above_eq
  {L : Real}
-- given
  (f : Nat -> Nat -> Real)
  (a : Nat -> Real)
  (prescribed : Nat -> Nat)
  (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
  (hhorizontal : Tendsto a atTop (nhds L)) :
-- imply
  exists lower : Nat -> Nat, (forall k, prescribed k <= lower k) /\ forall m : Nat -> Nat, (forall k, lower k <= m k) -> Tendsto (fun k => f k (m k)) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierD.exists_nat_uniform_lower_tendsto_above f a prescribed hvertical hhorizontal

/--
[fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (fkRectBalancedShareSpectralGap q r k)) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto hq r k

/--
[fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (fkRectBalancedSectorNormalizationVerticalRate hq r k)) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_vertical_negLog_tendsto_rate hq r k

/--
[tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  Tendsto (fkRectBalancedSectorNormalizationVerticalRate hq r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap hq r hperc hgap

/--
[exists_fkRectBalancedNormalization_spectralHeightLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma exists_fkRectBalancedNormalization_spectralHeightLower_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  exists heightLower : Nat -> Nat, (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k) /\ forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectBalancedNormalization_spectralHeightLower hq r hperc hgap

/--
[fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_unconditional_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_unconditional hq r hr hperc hgap

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hgap : forall r : Nat, 2 <= r -> Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional hq hhard hcross hgap

/--
[exists_fkRectBalancedShare_spectralHeightLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma exists_fkRectBalancedShare_spectralHeightLower_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  exists heightLower : Nat -> Nat, (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k) /\ forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectBalancedShare_spectralHeightLower hq r hgap

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_balancedShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_balancedShare_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hnoLoop : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hshare : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_noLoop_balancedShare hq r hr heightLower hwind hnoLoop hshare

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_balancedShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_balancedShare_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (crossingThreshold : (Nat -> Nat) -> Nat -> Nat)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hsmall : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> forall k, let R := fkRectFixedChargeVerticalFamily r k (m k) let n := crossingThreshold m k Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2)
  (hwidth : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => ((fkRectFixedChargeVerticalFamily r k (m k)).width : Real) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hthreshold : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => (crossingThreshold m k : Real) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hheight : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop atTop)
  (hshare : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_balancedShare hq r hr heightLower crossingThreshold hwind hsmall hwidth hthreshold hheight hshare

/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_balancedShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_balancedShare_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (heightLower : Nat -> Nat)
  (hPIMS : forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= heightLower k)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hwind : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hshare : forall m : Nat -> Nat, (forall k, heightLower k <= m k) -> Tendsto (fun k => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k (m k)) q) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_balancedShare hq r hr heightLower hPIMS hperc hwind hshare

/--
[fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap_eq
  {q xiInv : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 2 <= r)
  (hperc : let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) mu.real (Percolation.percolationEvent 2) = 0)
  (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap hq r hr hperc hscheduled

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap hq hhard hcross hscheduled

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 /\ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 /\ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) : Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) (hasInfiniteClusterEvent 2) = 1 /\ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) /\ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap hq hhard hcross hscheduled


-- created on 2026-10-23
