/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part7


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCentralConfigurationMatching_injective :
    Function.Injective sixVertexFourByTwoCentralConfigurationMatching := by
  intro first second heq
  apply sixVertexFourByTwoCentralSourceEquiv.symm.injective
  apply sixVertexFourByTwoCentralIndexMatching_injective
  apply Subtype.ext
  apply sixVertexFourByTwoCentralTargetEquiv.injective
  exact heq

theorem sixVertexFourByTwoCentralConfigurationMatching_components_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    (sixVertexFourByTwoCentralConfigurationMatching source).1 ≠
      (sixVertexFourByTwoCentralConfigurationMatching source).2 := by
  intro heq
  let target := sixVertexFourByTwoCentralIndexMatching
    (sixVertexFourByTwoCentralSourceEquiv.symm source)
  apply target.2
  apply sixVertexFourByTwoSectorTwoEquiv.injective
  simpa [sixVertexFourByTwoCentralConfigurationMatching,
    sixVertexFourByTwoCentralTargetEquiv, target] using heq

theorem sixVertexFourByTwoCentralConfigurationMatching_totalC
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralConfigurationMatching source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  let index := sixVertexFourByTwoCentralSourceEquiv.symm source
  have hsource := sixVertexFourByTwoCentralSourceEquiv.apply_symm_apply source
  calc
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralConfigurationMatching source) =
        4 * (sixVertexFourByTwoCentralTargetGrade
          (sixVertexFourByTwoCentralIndexMatching index)).val := by
            unfold sixVertexFourByTwoCentralConfigurationMatching
            rw [sixVertexFourByTwoCentralTargetIndex_totalC]
    _ = 4 * (sixVertexFourByTwoCentralSourceGrade index).val := by
      rw [sixVertexFourByTwoCentralIndexMatching_grade]
    _ = sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralSourceEquiv index) :=
      (sixVertexFourByTwoCentralSourceIndex_totalC index).symm
    _ = sixVertexConfigurationPairTotalCPhysical source := by rw [hsource]

end
end StatMech.FrontierD
