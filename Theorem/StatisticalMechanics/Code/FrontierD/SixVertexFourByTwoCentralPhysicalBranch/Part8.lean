/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC
    (source : SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralPhysicalSourceEmbedding source) =
      sixVertexConfigurationPairTotalCPhysical source := rfl


end
end StatMech.FrontierD
