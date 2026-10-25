/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part8


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width where
  branch choice :=
    sixVertexFourByTwoCentralPhysicalSourceEmbedding.trans
      (sixVertexFourByTwoCentralPhysicalBranch choice)
  distinct source := by
    exact sixVertexFourByTwoCentralPhysicalBranch_distinct
      (sixVertexFourByTwoCentralPhysicalSourceEmbedding source)
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source ≤
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoCentralPhysicalBranch false
              (sixVertexFourByTwoCentralPhysicalSourceEmbedding source)) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoCentralPhysicalBranch true
              (sixVertexFourByTwoCentralPhysicalSourceEmbedding source))
    rw [sixVertexFourByTwoCentralPhysicalBranch_totalC,
      sixVertexFourByTwoCentralPhysicalBranch_totalC]
    simp only [sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC]
    omega

end
end StatMech.FrontierD
