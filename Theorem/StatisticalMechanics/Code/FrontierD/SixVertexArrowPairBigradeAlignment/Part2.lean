/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexArrowTrueStrandSlotCount omega =
      2 * sixVertexArrowCheckerHorizontalAgreementCount omega := by
  unfold sixVertexArrowTrueStrandSlotCount
  rw [Fintype.card_congr (sixVertexArrowTrueStrandSlotEquiv omega)]
  simp [sixVertexArrowCheckerHorizontalAgreementCount]
  omega

end
end StatMech.FrontierD
