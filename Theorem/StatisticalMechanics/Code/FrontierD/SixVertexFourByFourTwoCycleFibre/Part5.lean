/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowZero_first
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowZero p).1) =
      (sixVertexFourByFourAuditedRowZero p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowZero_second
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowZero p).2) =
      (sixVertexFourByFourAuditedRowZero p).2 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_first
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowMiddle p).1) =
      (sixVertexFourByFourAuditedRowMiddle p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_second
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowMiddle p).2) =
      (sixVertexFourByFourAuditedRowMiddle p).2 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowLast_first
    (p : Fin 4) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowLast p).1) =
      (sixVertexFourByFourAuditedRowLast p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowLast_second
    (p : Fin 4) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowLast p).2) =
      (sixVertexFourByFourAuditedRowLast p).2 := by
  fin_cases p <;> decide

end
end StatMech.FrontierD
