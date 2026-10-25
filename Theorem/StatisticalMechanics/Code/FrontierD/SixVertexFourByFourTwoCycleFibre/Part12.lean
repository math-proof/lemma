/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part12


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAudited_selectedColumns_constant
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) :
    SixVertexFourByFourAuditedSelectedColumnsConstantStatement
      p firstSeam secondSeam := by
  unfold SixVertexFourByFourAuditedSelectedColumnsConstantStatement
  intro hfirst hsecond hfirstSector hsecondSector
  constructor
  · intro y
    change sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam y
        (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1 = false
    have hcount := sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p firstSeam y hfirst hfirstSector
    have heven := sixVertexFourByFourAuditedParamSourceFirst_even
      p firstSeam y hfirst hfirstSector
    simpa [sixVertexFourByFourAuditedRepairColumns] using
      sixVertexFourByFourSelectedFirst_false
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam y)
        firstSeam hcount heven
  · intro y
    change sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam y
        (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2 = true
    have hcount := sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p secondSeam y hsecond hsecondSector
    have heven := sixVertexFourByFourAuditedParamSourceSecond_even
      p secondSeam y hsecond hsecondSector
    exact sixVertexFourByFourSelectedSecond_true
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam y)
      firstSeam secondSeam hcount heven

theorem sixVertexFourByFourAuditedParamMatching_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) :
    SixVertexFourByFourAuditedParamMatchingStatement p firstSeam secondSeam := by
  intro hfirst hsecond hfirstSector hsecondSector
  have hcolumns := sixVertexFourByFourAudited_selectedColumns_constant
    p firstSeam secondSeam hfirst hsecond hfirstSector hsecondSector
  unfold SixVertexFourByFourValidColumnRepair
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sixVertexFourByFourToggleVerticalColumn_iceRule _ _ false
      hcolumns.1 hfirst
  · exact sixVertexFourByFourToggleVerticalColumn_iceRule _ _ true
      hcolumns.2 hsecond
  · have hup := sixVertexFourByFourToggleVerticalColumn_upCount_false
      (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1
      (svFinLast sixVertexFourByFourTorus.height_pos)
      (hcolumns.1 (svFinLast sixVertexFourByFourTorus.height_pos))
    change sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).1
            (sixVertexFourByFourAuditedParamSourceFirst p firstSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2
    calc
      _ = sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByFourTorus
              (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
              (svFinLast sixVertexFourByFourTorus.height_pos)) + 1 := hup
      _ = 2 := by rw [hfirstSector]
  · have hup := sixVertexFourByFourToggleVerticalColumn_upCount_true
      (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2
      (svFinLast sixVertexFourByFourTorus.height_pos)
      (hcolumns.2 (svFinLast sixVertexFourByFourTorus.height_pos))
    change sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).2
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2
    have htargetPlus : sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).2
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) + 1 = 3 :=
      hup.symm.trans hsecondSector
    omega

end
end StatMech.FrontierD
