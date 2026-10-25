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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part3
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width where
  branch choice :=
    sixVertexFourByTwoPhysicalSourceEmbedding.trans
      (sixVertexFourByTwoPhysicalBranch choice)
  distinct source := by
    exact sixVertexFourByTwoPhysicalBranch_distinct
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source <=
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoPhysicalBranch false
              (sixVertexFourByTwoPhysicalSourceEmbedding source)) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoPhysicalBranch true
              (sixVertexFourByTwoPhysicalSourceEmbedding source))
    have hfalse := sixVertexFourByTwoPhysicalBranch_totalC false
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
    have htrue := sixVertexFourByTwoPhysicalBranch_totalC true
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
    rw [hfalse, htrue]
    simp only [sixVertexFourByTwoPhysicalSourceEmbedding_totalC]
    omega


end
end StatMech.FrontierD
