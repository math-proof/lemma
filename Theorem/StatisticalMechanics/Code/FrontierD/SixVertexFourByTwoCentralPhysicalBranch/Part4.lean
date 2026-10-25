/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCentralIndexMatching_injective :
    Function.Injective sixVertexFourByTwoCentralIndexMatching := by
  intro first second heq
  apply sixVertexFourByTwoCentralRawMatching_certificate.1
  exact congrArg Subtype.val heq

theorem sixVertexFourByTwoCentralIndexMatching_grade
    (source : sixVertexFourByTwoCentralSourceIndex) :
    sixVertexFourByTwoCentralSourceGrade source =
      sixVertexFourByTwoCentralTargetGrade
        (sixVertexFourByTwoCentralIndexMatching source) :=
  sixVertexFourByTwoCentralRawMatching_certificate.2 source |>.2

end
end StatMech.FrontierD
