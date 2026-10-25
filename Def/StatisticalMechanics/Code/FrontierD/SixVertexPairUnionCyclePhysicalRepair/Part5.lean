/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoPairUnionCycleOffDiagonalEmbedding :
    SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne]) where
  target :=
    { toFun := sixVertexFourByTwoConfigurationPairMatching
      inj' := sixVertexFourByTwoConfigurationPairMatching_injective }
  related := sixVertexFourByTwoConfigurationPairMatching_fineRelated
  layers_ne := sixVertexFourByTwoConfigurationPairMatching_layers_ne


def sixVertexFourByTwoPairUnionCyclePairedRepairs :
    SixVertexConfigurationPairUnionCyclePairedRepairs
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne]) :=
  sixVertexFourByTwoPairUnionCycleOffDiagonalEmbedding.toPairedRepairs

end
end StatMech.FrontierD
