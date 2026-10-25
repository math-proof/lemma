/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
import Structure.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 <= r)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q xiInv) :
    ((r - 1 : Nat) : Real) * xiInv <=
      (r : Real) * fkQgt4SixVertexGapRate q := by
  obtain ⟨heightLower, hPIMS, hnormalization⟩ :=
    exists_fkRectBalancedNormalization_spectralHeightLower hq r hperc
      (hscheduled.spectralGap r hr)
  apply fkQgt4_fixedCharge_bound_of_uniformDiagonalLimitsAbove
    hq r hr heightLower
  · intro m hm
    apply hscheduled.winding r hr m
    intro k
    exact (hPIMS k).trans (hm k)
  · exact hnormalization


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
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
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_fixedCharge
    hq hhard hcross
  intro r hr
  apply fkQgt4_fixedCharge_bound_of_freePIMS_and_spectralGap hq r hr
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact hscheduled

set_option maxHeartbeats 800000 in


theorem
    fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
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
    (hscheduled : FKQgt4BoundaryIncidenceScheduledSpectralGap q
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
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
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap
      hq hhard hcross hscheduled

end
end StatMech.FrontierD
