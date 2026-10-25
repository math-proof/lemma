/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    sixVertexArrowPairTrueStrandSlotCount omega eta =
      2 * (sixVertexArrowCheckerHorizontalAgreementCount omega +
        sixVertexArrowCheckerHorizontalAgreementCount eta) := by
  unfold sixVertexArrowPairTrueStrandSlotCount
  rw [Fintype.card_congr
      (sixVertexArrowPairTrueStrandSlotEquivSum omega eta),
    Fintype.card_sum,
    ← sixVertexArrowTrueStrandSlotCount,
    ← sixVertexArrowTrueStrandSlotCount,
    sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment,
    sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment]
  omega

end
end StatMech.FrontierD
