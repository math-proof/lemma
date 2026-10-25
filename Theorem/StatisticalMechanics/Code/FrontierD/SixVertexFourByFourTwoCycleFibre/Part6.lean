/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed
    (p : SixVertexFourByFourAuditedHorizontalParameters) (y : Fin 4) :
    ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsFirst p y =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i) := by
  fin_cases y <;> exact ⟨_, rfl⟩

theorem sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed
    (p : SixVertexFourByFourAuditedHorizontalParameters) (y : Fin 4) :
    ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsSecond p y =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i) := by
  fin_cases y <;> exact ⟨_, rfl⟩

end
end StatMech.FrontierD
