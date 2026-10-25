/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part8


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCentralPhysicalBranch_distinct source :
    sixVertexFourByTwoCentralPhysicalBranch false source ≠
      sixVertexFourByTwoCentralPhysicalBranch true source := by
  intro heq
  have hcomponents := congrArg Prod.fst heq
  exact sixVertexFourByTwoCentralConfigurationMatching_components_ne source
    (by simpa [sixVertexFourByTwoCentralPhysicalBranch] using hcomponents)

theorem sixVertexFourByTwoCentralPhysicalBranch_totalC
    (choice : Bool) (source) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralPhysicalBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  cases choice <;>
    simpa [sixVertexFourByTwoCentralPhysicalBranch,
      sixVertexConfigurationPairTotalCPhysical, Nat.add_comm] using
      sixVertexFourByTwoCentralConfigurationMatching_totalC source

theorem sixVertexFourByTwoSectorTwo_pos :
    0 < sixVertexFourByTwoSectorTwo.val := by
  norm_num [sixVertexFourByTwoSectorTwo]

theorem sixVertexFourByTwoSectorTwo_lt_width :
    sixVertexFourByTwoSectorTwo.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorTwo, sixVertexFourByTwoTorus]

end
end StatMech.FrontierD
