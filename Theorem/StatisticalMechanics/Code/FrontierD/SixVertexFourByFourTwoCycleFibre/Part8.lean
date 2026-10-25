/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part8


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourCompletedVerticalMask_row
    (horizontalMask seamMask : Nat) (x y : Fin 4) :
    (sixVertexFourByFourArrowsOfMasks horizontalMask
      (sixVertexFourByFourCompletedVerticalMask horizontalMask seamMask)).vertical
        (x, y) =
      sixVertexFourByFourCompletedVerticalRow horizontalMask seamMask y x := by
  unfold sixVertexFourByFourArrowsOfMasks
  unfold sixVertexFourByFourCompletedVerticalMask
  unfold sixVertexFourByFourCompletedVerticalRow
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change sixVertexFourByFourCompletedVerticalColumn horizontalMask seamMask
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).2
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).1 = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

theorem sixVertexFourByFourCompletedVerticalColumn_auditedFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (seam x y : Fin 4) :
    sixVertexFourByFourCompletedVerticalColumn
        (sixVertexFourByFourAuditedHorizontalMasks p).1
        (sixVertexFourByFourSectorOneSeamMask seam) x y =
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y x := by
  fin_cases y <;>
    simp [sixVertexFourByFourCompletedVerticalColumn,
      sixVertexFourByFourVerticalNext,
      sixVertexFourByFourAuditedHorizontalMasks,
      sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourNextVerticalRow,
      sixVertexFourByFourRowOfMask] <;> rfl

theorem sixVertexFourByFourCompletedVerticalColumn_auditedSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (seam x y : Fin 4) :
    sixVertexFourByFourCompletedVerticalColumn
        (sixVertexFourByFourAuditedHorizontalMasks p).2
        (sixVertexFourByFourSectorThreeSeamMask seam) x y =
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y x := by
  fin_cases y <;>
    simp [sixVertexFourByFourCompletedVerticalColumn,
      sixVertexFourByFourVerticalNext,
      sixVertexFourByFourAuditedHorizontalMasks,
      sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourNextVerticalRow,
      sixVertexFourByFourRowOfMask] <;> rfl

theorem sixVertexFourByFour_rowIce
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hice : omega.IceRule) (y : Fin 4) :
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (svTorusVerticalRows sixVertexFourByFourTorus omega
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (svTorusVerticalRows sixVertexFourByFourTorus omega y)
      (svTorusHorizontalRows sixVertexFourByFourTorus omega y) := by
  intro x
  simpa [svHorizontalIncomingCount, svTorusVerticalRows,
    svTorusHorizontalRows, SixVertexArrows.incomingCount,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using hice (x, y)

theorem sixVertexFourByFour_verticalRowCount_eq_last
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hice : omega.IceRule) (y : Fin 4) :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus omega
          (svFinLast sixVertexFourByFourTorus.height_pos)) := by
  have h0 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 0)
  have h1 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 1)
  have h2 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 2)
  have h3 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 3)
  fin_cases y <;>
    simp [SixVertexArrows.cyclicPred, svFinLast,
      sixVertexFourByFourTorus] at h0 h1 h2 h3 ⊢ <;>
    omega

end
end StatMech.FrontierD
