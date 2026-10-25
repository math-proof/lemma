/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCentralSourceIndex_totalC
    (source : sixVertexFourByTwoCentralSourceIndex) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralSourceEquiv source) =
      4 * (sixVertexFourByTwoCentralSourceGrade source).val := by
  change
    sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorOneConfiguration source.1).1 +
        sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorThreeConfiguration source.2).1 = _
  simp only [sixVertexFourByTwoSectorThreeConfiguration,
    sixVertexArrowsComplement_cTypeCount,
    sixVertexFourByTwoSectorOneConfiguration_cTypeCount]
  simp [sixVertexFourByTwoCentralSourceGrade]
  omega

theorem sixVertexFourByTwoCentralTargetIndex_totalC
    (target : sixVertexFourByTwoCentralTargetIndex) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralTargetEquiv target.1) =
      4 * (sixVertexFourByTwoCentralTargetGrade target).val := by
  change
    sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorTwoConfiguration target.1.1).1 +
        sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorTwoConfiguration target.1.2).1 = _
  simp only [sixVertexFourByTwoSectorTwoConfiguration_cTypeCount]
  simp [sixVertexFourByTwoCentralTargetGrade]
  omega

end
end StatMech.FrontierD
