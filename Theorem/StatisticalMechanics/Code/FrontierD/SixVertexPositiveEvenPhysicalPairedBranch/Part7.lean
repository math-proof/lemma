/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part6
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem
    tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches
    {q : Real} (hq : 4 < q) (r : Nat)
    (hbranches :
      SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact
    sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))
      (by linarith [two_lt_fkQgt4SixVertexWeight hq])
      (hbranches r k)


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
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
    (hbranches :
      SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches
      hq r hbranches

end
end StatMech.FrontierD
