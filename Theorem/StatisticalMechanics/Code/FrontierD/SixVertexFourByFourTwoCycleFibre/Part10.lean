/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part10


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAuditedParamSourceSecond_even
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  have hcountZero :=
    sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p seam 0 hice hsector
  have hcountZero' : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p.1).2)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam))) = 3 := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond] using hcountZero
  have hzero :
      sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 0) =
        sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorThreeSeamMask seam)) := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond] using
      sixVertexFourByFourSecondRowZero_even p.1 seam hcountZero'
  have h01 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 1 hice
  have h12 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 2 hice
  have h23 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 3 hice
  simp [SixVertexArrows.cyclicPred] at h01 h12 h23
  fin_cases y
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h12.symm.trans (h01.symm.trans hzero)
  · exact h23.symm.trans (h12.symm.trans (h01.symm.trans hzero))

theorem sixVertexFourByFourSelectedFirst_false
    (row : SixVertexRow 4) (seam : Fin 4)
    (hcount : sixVertexUpCount row = 1)
    (heven : sixVertexFourByFourEvenUpCount row =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) :
    row (![1, 0, 1, 0] seam) = false := by
  fin_cases seam <;> revert row <;> decide

theorem sixVertexFourByFourSelectedSecond_true
    (row : SixVertexRow 4) (firstSeam secondSeam : Fin 4)
    (hcount : sixVertexUpCount row = 3)
    (heven : sixVertexFourByFourEvenUpCount row =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask secondSeam))) :
    row (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2 =
      true := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> revert row <;> decide

end
end StatMech.FrontierD
