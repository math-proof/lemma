/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoConfiguration_cGrade_certificate :
    (∀ i : Fin 28,
      sixVertexCheckerHorizontalNontransitionCount
          (sixVertexFourByTwoSectorOneConfiguration i).1 =
        4 * (sixVertexFourByTwoSectorOneCGrade i).val) ∧
    (∀ i : Fin 50,
      sixVertexCheckerHorizontalNontransitionCount
          (sixVertexFourByTwoSectorTwoConfiguration i).1 =
        4 * (sixVertexFourByTwoSectorTwoCGrade i).val) := by
  decide +revert

theorem sixVertexFourByTwoSectorOneConfiguration_cTypeCount (i : Fin 28) :
    sixVertexTorusCTypeCount
        (sixVertexFourByTwoSectorOneConfiguration i).1 =
      4 * (sixVertexFourByTwoSectorOneCGrade i).val := by
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount]
  exact sixVertexFourByTwoConfiguration_cGrade_certificate.1 i

theorem sixVertexFourByTwoSectorTwoConfiguration_cTypeCount (i : Fin 50) :
    sixVertexTorusCTypeCount
        (sixVertexFourByTwoSectorTwoConfiguration i).1 =
      4 * (sixVertexFourByTwoSectorTwoCGrade i).val := by
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount]
  exact sixVertexFourByTwoConfiguration_cGrade_certificate.2 i

end
end StatMech.FrontierD
