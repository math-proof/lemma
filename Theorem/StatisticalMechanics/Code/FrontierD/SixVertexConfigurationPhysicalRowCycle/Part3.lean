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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexMarkedSectorRowCycleGradeFiber
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    Fintype.card
        {rows : SixVertexMarkedSectorRowCycle T sector //
          sixVertexMarkedSectorRowCycleTotalC rows = totalC} =
      sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
  rw [Fintype.card_congr
    (sixVertexMarkedSectorRowCycleGradeFiberEquiv T sector totalC),
    Fintype.card_sigma]
  unfold sixVertexMarkedSectorRowCycleGradeCount
  apply Finset.sum_congr rfl
  intro vertical _
  by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1 = totalC
  · rw [if_pos hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_true,
      Finset.card_univ, Fintype.card_pi]
  · rw [if_neg hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_false,
      Finset.card_empty]


end
end StatMech.FrontierD
