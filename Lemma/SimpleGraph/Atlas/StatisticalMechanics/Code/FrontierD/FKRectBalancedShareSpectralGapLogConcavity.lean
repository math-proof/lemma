import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
open Filter MeasureTheory Topology StatMech StatMech.FrontierD


/--
[fkRectBalancedShareSpectralGap_eq_zero_of_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkRectBalancedShareSpectralGap_eq_zero_of_logConcave_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q)
  (hlc : SixVertexSectorPerronLogConcave (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  fkRectBalancedShareSpectralGap q r k = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k hlc

/--
[fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q)
  (hlc : SixVertexSectorTraceLogConcave (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  fkRectBalancedShareSpectralGap q r k = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave hq r k hlc

/--
[fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q)
  (hHall : SixVertexPositiveEvenTraceKeyCapacityHall (sixVertexFourWidth r (k + 1)) (sixVertexFourWidth_pos r (k + 1)) (sixVertexFourWidth_even r (k + 1))) :
-- imply
  fkRectBalancedShareSpectralGap q r k = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall hq r k hHall

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_logConcave_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hlc : ∀ᶠ k in atTop, SixVertexSectorPerronLogConcave (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_logConcave hq r hlc

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hlc : ∀ᶠ k in atTop, SixVertexSectorTraceLogConcave (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave hq r hlc

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall hq r hHall

/--
[fkRectBalancedShareSpectralGap_eq_base_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkRectBalancedShareSpectralGap_eq_base_shift_eq
  {q : Real}
  {r k : Nat} :
-- imply
  fkRectBalancedShareSpectralGap q r k = fkRectBalancedShareSpectralGap q 0 (k + r) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedShareSpectralGap_eq_base_shift q r k

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_base_eq
  {q : Real}
  {r : Nat}
-- given
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0) atTop (nhds 0)) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_base hgap r

/--
[FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity.toSpectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma toSpectralGap_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (h : FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q xiInv) :
-- imply
  FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv := by
-- proof
  apply StatMech.FrontierD.FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity.toSpectralGap hq h

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hscheduled : FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity hq hhard hcross hscheduled

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_unconditional_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (htrace : forall r : Nat, 2 <= r -> forall k : Nat, SixVertexSectorTraceLogConcave (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_unconditional hq hhard hcross htrace

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_keyCapacityHall_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_keyCapacityHall_unconditional_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_keyCapacityHall_unconditional hq hhard hcross hHall

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hgap : forall r : Nat, 2 <= r -> Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 /\ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 /\ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) : Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) (hasInfiniteClusterEvent 2) = 1 /\ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) /\ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional hq hhard hcross hgap

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_baseSpectralGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_baseSpectralGap_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0) atTop (nhds 0)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 /\ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 /\ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) : Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) (hasInfiniteClusterEvent 2) = 1 /\ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) /\ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_baseSpectralGap hq hhard hcross hgap

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_keyCapacityHall_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 /\ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 /\ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) : Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) (hasInfiniteClusterEvent 2) = 1 /\ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) /\ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_keyCapacityHall hq hhard hcross hHall


-- created on 2026-10-23
