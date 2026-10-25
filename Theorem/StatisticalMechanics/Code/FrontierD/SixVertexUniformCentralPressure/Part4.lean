/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
import Def.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hbound : SixVertexUniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have htop :=
    sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_even r (k + 1)) hc hbound
  unfold fkRectBalancedShareSpectralGap
  rw [htop]
  simp [sixVertexLambda]

theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
    {q : Real} (hq : 4 < q) (r : Nat)
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  exact fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound
    hq r k (hbound r k)

theorem
    tendsto_fkRectBalancedNormalizationRate_zero_of_crossingFloor_uniformTrace
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
    (r : Nat)
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    Tendsto (fkRectBalancedSectorNormalizationVerticalRate hq r)
      atTop (nhds 0) := by
  apply
    tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap
      hq r
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact
      tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
        hq r hbound

theorem
    fkQgt4_windingBridge_of_crossingFloor_uniformCentralTrace
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
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
      hq r hbound

end
end StatMech.FrontierD
