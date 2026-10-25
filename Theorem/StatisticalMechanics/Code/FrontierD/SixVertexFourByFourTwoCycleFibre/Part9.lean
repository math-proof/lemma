/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part9


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAuditedParamSourceFirst_eq_completedMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamSourceFirst p seam =
      sixVertexFourByFourArrowsOfMasks
        (sixVertexFourByFourAuditedHorizontalMasks p).1
        (sixVertexFourByFourCompletedVerticalMask
          (sixVertexFourByFourAuditedHorizontalMasks p).1
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases y <;>
      simp [sixVertexFourByFourAuditedParamSourceFirst,
        sixVertexFourByFourArrowsOfMasks,
        sixVertexFourByFourAuditedHorizontalMasks,
        sixVertexFourByFourAuditedParamHorizontalRowsFirst] <;> rfl
  · funext v
    rcases v with ⟨x, y⟩
    symm
    calc
      _ = sixVertexFourByFourCompletedVerticalRow
            (sixVertexFourByFourAuditedHorizontalMasks p).1
            (sixVertexFourByFourSectorOneSeamMask seam) y x :=
        sixVertexFourByFourCompletedVerticalMask_row _ _ x y
      _ = _ := sixVertexFourByFourCompletedVerticalColumn_auditedFirst
        p seam x y

theorem sixVertexFourByFourAuditedParamSourceSecond_eq_completedMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamSourceSecond p seam =
      sixVertexFourByFourArrowsOfMasks
        (sixVertexFourByFourAuditedHorizontalMasks p).2
        (sixVertexFourByFourCompletedVerticalMask
          (sixVertexFourByFourAuditedHorizontalMasks p).2
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases y <;>
      simp [sixVertexFourByFourAuditedParamSourceSecond,
        sixVertexFourByFourArrowsOfMasks,
        sixVertexFourByFourAuditedHorizontalMasks,
        sixVertexFourByFourAuditedParamHorizontalRowsSecond] <;> rfl
  · funext v
    rcases v with ⟨x, y⟩
    symm
    calc
      _ = sixVertexFourByFourCompletedVerticalRow
            (sixVertexFourByFourAuditedHorizontalMasks p).2
            (sixVertexFourByFourSectorThreeSeamMask seam) y x :=
        sixVertexFourByFourCompletedVerticalMask_row _ _ x y
      _ = _ := sixVertexFourByFourCompletedVerticalColumn_auditedSecond
        p seam x y

theorem sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) = 1 := by
  have hcount := sixVertexFourByFour_verticalRowCount_eq_last
    (sixVertexFourByFourAuditedParamSourceFirst p seam) hice y
  exact (by
    simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using hcount.trans hsector)

theorem sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) = 3 := by
  have hcount := sixVertexFourByFour_verticalRowCount_eq_last
    (sixVertexFourByFourAuditedParamSourceSecond p seam) hice y
  exact (by
    simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using hcount.trans hsector)

theorem sixVertexFourByFourAuditedParamSourceFirst_evenStep
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam
          (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) := by
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed p y
  have hrow := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceFirst p seam) hice y
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y) at hrow
  rw [hi] at hrow
  exact sixVertexFourByFourEvenUpCount_preserved i _ _ hrow

theorem sixVertexFourByFourAuditedParamSourceSecond_evenStep
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam
          (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) := by
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed p y
  have hrow := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceSecond p seam) hice y
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y) at hrow
  rw [hi] at hrow
  exact sixVertexFourByFourEvenUpCount_preserved i _ _ hrow

theorem sixVertexFourByFourAuditedParamSourceFirst_even
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  have hcountZero :=
    sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p seam 0 hice hsector
  have hcountZero' : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p.1).1)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) = 1 := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst] using hcountZero
  have hzero :
      sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 0) =
        sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorOneSeamMask seam)) := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst] using
      sixVertexFourByFourFirstRowZero_even p.1 seam hcountZero'
  have h01 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 1 hice
  have h12 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 2 hice
  have h23 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 3 hice
  simp [SixVertexArrows.cyclicPred] at h01 h12 h23
  fin_cases y
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h12.symm.trans (h01.symm.trans hzero)
  · exact h23.symm.trans (h12.symm.trans (h01.symm.trans hzero))

end
end StatMech.FrontierD
