/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedCoordinates_card :
    Fintype.card SixVertexFourByFourAuditedCoordinates = 512 := by
  decide

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedHorizontalParameters_card :
    Fintype.card SixVertexFourByFourAuditedHorizontalParameters = 16384 := by
  decide

theorem sixVertexFourByFourAuditedCoordinateParameterImage_card :
    sixVertexFourByFourAuditedCoordinateParameterImage.card = 512 := by
  rw [sixVertexFourByFourAuditedCoordinateParameterImage,
    Finset.card_image_iff.mpr
      sixVertexFourByFourAuditedCoordinateParameters_injective.injOn]
  exact sixVertexFourByFourAuditedCoordinates_card

theorem sixVertexFourByFourAuditedCoordinateParameterComplement_card :
    sixVertexFourByFourAuditedCoordinateParameterComplement.card = 15872 := by
  rw [sixVertexFourByFourAuditedCoordinateParameterComplement,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    sixVertexFourByFourAuditedCoordinateParameterImage_card,
    sixVertexFourByFourAuditedHorizontalParameters_card]

end
end StatMech.FrontierD
