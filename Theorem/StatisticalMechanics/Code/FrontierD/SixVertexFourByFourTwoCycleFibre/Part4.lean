/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourEvenUpCount_preserved
    (i : Fin 6) (previous current : SixVertexRow 4)
    (hice : svHorizontalIce (by norm_num) previous current
      (sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i))) :
    sixVertexFourByFourEvenUpCount previous =
      sixVertexFourByFourEvenUpCount current := by
  unfold svHorizontalIce svHorizontalIncomingCount at hice
  unfold sixVertexFourByFourEvenUpCount at ⊢
  unfold sixVertexFourByFourRowOfMask at hice
  unfold sixVertexFourByFourAllowedHorizontalMask at hice
  fin_cases i <;> decide +revert

theorem sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq
    (i : Fin 6) (below : SixVertexRow 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAllowedHorizontalMask i)) below) =
      sixVertexUpCount below) :
    svHorizontalIce (by norm_num) below
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAllowedHorizontalMask i)) below)
      (sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i)) := by
  unfold svHorizontalIce svHorizontalIncomingCount
  fin_cases i <;> revert below <;> decide

theorem sixVertexFourByFourFirstRowZero_even
    (p0 : Fin 16) (seam : Fin 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p0).1)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) = 1) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero p0).1)
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorOneSeamMask seam))) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  fin_cases p0 <;> fin_cases seam <;> revert hcount <;> decide

theorem sixVertexFourByFourSecondRowZero_even
    (p0 : Fin 16) (seam : Fin 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p0).2)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam))) = 3) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero p0).2)
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorThreeSeamMask seam))) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  fin_cases p0 <;> fin_cases seam <;> revert hcount <;> decide

end
end StatMech.FrontierD
