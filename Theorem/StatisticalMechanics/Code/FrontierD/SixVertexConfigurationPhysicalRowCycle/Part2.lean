/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexArrows_isCType_iff_verticalRow_ne
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (i : Fin T.width) (j : Fin T.height) :
    omega.IsCType (i, j) ↔
      svTorusVerticalRows T omega
          (SixVertexArrows.cyclicPred T.height_pos j) i ≠
        svTorusVerticalRows T omega j i := by
  have hrow :=
    (sixVertexIceRule_iff_horizontalRowTransitions omega).mp homega j
  have hc := svHorizontalIsC_iff_ne T.width_pos hrow i
  simpa [SixVertexArrows.IsCType, svHorizontalIsC,
    svTorusHorizontalRows, svTorusVerticalRows] using hc

theorem sixVertexTorusCTypeCount_eq_rowCycleTotalC
    {T : EvenTorus} {sector : Fin (T.width + 1)}
    (omega : SixVertexMarkedSectorConfiguration T sector) :
    sixVertexTorusCTypeCount omega.1 =
      sixVertexMarkedSectorRowCycleTotalC
        (sixVertexMarkedSectorConfigurationEquivRowCycle T sector omega) := by
  classical
  unfold sixVertexTorusCTypeCount sixVertexMarkedSectorRowCycleTotalC
    sixVertexRowDistance
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_congr
    (sixVertexArrows_isCType_iff_verticalRow_ne omega.1 omega.2.1 i j)
    rfl rfl]
  rfl


end
end StatMech.FrontierD
