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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexMarkedSectorRowCyclePairGradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorRowCycle T left ×
            SixVertexMarkedSectorRowCycle T right //
          sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} =
      sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC := by
  rw [Fintype.card_congr
    (sixVertexMarkedSectorRowCyclePairGradeFiberEquiv
      T left right totalC), Fintype.card_sigma]
  unfold sixVertexMarkedSectorRowCyclePairGradeCount
  apply Finset.sum_congr rfl
  intro vertical _
  by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1.1 +
      sixVertexVerticalRowsTotalC vertical.2.1 = totalC
  · rw [if_pos hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_true,
      Finset.card_univ, Fintype.card_prod, Fintype.card_pi]
  · rw [if_neg hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_false,
      Finset.card_empty]


theorem sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC =
      ∑ k : Fin (totalC + 1),
        sixVertexMarkedSectorRowCycleGradeCount T left k.val *
          sixVertexMarkedSectorRowCycleGradeCount
            T right (totalC - k.val) := by
  rw [← card_sixVertexMarkedSectorRowCyclePairGradeFiber]
  simp only [← Nat.card_eq_fintype_card]
  change Nat.card
      {pair : SixVertexMarkedSectorRowCycle T left ×
          SixVertexMarkedSectorRowCycle T right //
        sixVertexMarkedSectorRowCycleTotalC pair.1 +
          sixVertexMarkedSectorRowCycleTotalC pair.2 = totalC} = _
  rw [natCard_natGradedPairFiber]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCycleGradeFiber,
    Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCycleGradeFiber]

end
end StatMech.FrontierD
