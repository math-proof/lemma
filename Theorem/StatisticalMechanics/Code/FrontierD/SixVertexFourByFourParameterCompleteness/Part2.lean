/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_decodedSeams_inverse (rowZero : Fin 16) :
    sixVertexFourByFourAuditedCoordinateRowZero
        (sixVertexFourByFourAuditedDecodedSeams rowZero).1 (sixVertexFourByFourAuditedDecodedSeams rowZero).2 =
      rowZero := by
  fin_cases rowZero <;> decide

theorem sixVertexFourByFourAudited_firstDecode_exists_of_count
    (row : SixVertexRow 4) (hcount : sixVertexUpCount row = 1) :
    exists state, sixVertexFourByFourAuditedFirstStateDecode row = some state := by
  cases hdecode : sixVertexFourByFourAuditedFirstStateDecode row with
  | some state => exact ⟨state, rfl⟩
  | none =>
      have hspec := sixVertexFourByFourAudited_firstStateDecode_spec row
      rw [hdecode] at hspec
      exact (hspec hcount).elim

theorem sixVertexFourByFourAudited_secondDecode_exists_of_count
    (row : SixVertexRow 4) (hcount : sixVertexUpCount row = 3) :
    exists state, sixVertexFourByFourAuditedSecondStateDecode row = some state := by
  cases hdecode : sixVertexFourByFourAuditedSecondStateDecode row with
  | some state => exact ⟨state, rfl⟩
  | none =>
      have hspec := sixVertexFourByFourAudited_secondStateDecode_spec row
      rw [hdecode] at hspec
      exact (hspec hcount).elim

theorem sixVertexFourByFourAudited_firstRow_eq_of_decode
    (row : SixVertexRow 4) (state : Fin 4)
    (hdecode : sixVertexFourByFourAuditedFirstStateDecode row = some state) :
    row = sixVertexFourByFourAuditedFirstStateRow state := by
  have hspec := sixVertexFourByFourAudited_firstStateDecode_spec row
  rw [hdecode] at hspec
  exact sixVertexFourByFourAudited_rowOfBits_injective hspec

theorem sixVertexFourByFourAudited_secondRow_eq_of_decode
    (row : SixVertexRow 4) (state : Fin 4)
    (hdecode : sixVertexFourByFourAuditedSecondStateDecode row = some state) :
    row = sixVertexFourByFourAuditedSecondStateRow state := by
  have hspec := sixVertexFourByFourAudited_secondStateDecode_spec row
  rw [hdecode] at hspec
  exact sixVertexFourByFourAudited_rowOfBits_injective hspec

@[simp] theorem sixVertexFourByFourAudited_firstDecode_state (state : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourAuditedFirstStateRow state) = some state := by
  fin_cases state <;> decide

@[simp] theorem sixVertexFourByFourAudited_secondDecode_state (state : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourAuditedSecondStateRow state) = some state := by
  fin_cases state <;> decide

@[simp] theorem sixVertexFourByFourAudited_nextVerticalRow_zero (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask 0) below = below := by
  rw [show sixVertexFourByFourRowOfMask 0 = fun _ => false by
    funext x
    fin_cases x <;> decide]
  exact sixVertexFourByFourAudited_nextVerticalRow_constant false below

@[simp] theorem sixVertexFourByFourAudited_nextVerticalRow_fifteen (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask 15) below = below := by
  rw [show sixVertexFourByFourRowOfMask 15 = fun _ => true by
    funext x
    fin_cases x <;> decide]
  exact sixVertexFourByFourAudited_nextVerticalRow_constant true below

theorem sixVertexFourByFourAudited_firstVerticalRow_three_eq_two
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 3 =
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 2 := by
  rcases p with ⟨rowZero, firstMiddle, secondMiddle, last⟩
  fin_cases last <;>
    simp [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedRowLast,
      sixVertexFourByFourAllowedHorizontalIndex,
      sixVertexFourByFourAllowedHorizontalMask]

theorem sixVertexFourByFourAudited_secondVerticalRow_three_eq_two
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 3 =
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 2 := by
  rcases p with ⟨rowZero, firstMiddle, secondMiddle, last⟩
  fin_cases last <;>
    simp [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedRowLast,
      sixVertexFourByFourAllowedHorizontalIndex,
      sixVertexFourByFourAllowedHorizontalMask]

end StatMech.FrontierD
