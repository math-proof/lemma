/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
import Structure.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
open Filter MeasureTheory Topology


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem
    FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity.toSpectralGap
    {q xiInv : Real} (hq : 4 < q)
    (h : FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q xiInv) :
    FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv := by
  refine ⟨h.winding, ?_⟩
  intro r hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
    hq r (Filter.Eventually.of_forall fun k => h.traceLogConcavity r hr k)


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hscheduled :
      FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity q
        (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
    hq hhard hcross (hscheduled.toSpectralGap hq)


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_traceLogConcavity_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (htrace : forall r : Nat, 2 <= r -> forall k : Nat,
      SixVertexSectorTraceLogConcave
        (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
      hq r (Filter.Eventually.of_forall fun k => htrace r hr k)


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_keyCapacityHall_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    hq r hHall

set_option maxHeartbeats 1600000 in


theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hgap : forall r : Nat, 2 <= r ->
      Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_winding
    hq hhard hcross
  exact
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross hgap

set_option maxHeartbeats 1600000 in


theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_baseSpectralGap
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0)
      atTop (nhds 0)) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_base hgap r

set_option maxHeartbeats 1600000 in


theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_keyCapacityHall
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    let hq0 : (0 : Real) < q := by linarith
    FK.IsFirstOrderTransition 2 hp hp1 hq0 /\
      FK.freeInfiniteVolume 2 hp hp1 hq0 ≠
        FK.wiredInfiniteVolume 2 hp hp1 hq0 /\
      ((FK.wiredInfiniteVolume 2 hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) :
        Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
          (hasInfiniteClusterEvent 2) = 1 /\
      Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q)) /\
      0 < fkQgt4SixVertexGapRate q := by
  apply
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    hq r hHall

end
end StatMech.FrontierD
