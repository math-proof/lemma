/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalSectorCompletion_eq_chooseCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      sixVertexHorizontalSectorCompletionChooseCount
        T sector horizontal := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · rw [sixVertexHorizontalSectorCompletionChooseCount,
      if_pos hcompletion]
    exact card_sixVertexHorizontalSectorCompletion_eq_choose
      (Classical.choice hcompletion) sector
  · rw [sixVertexHorizontalSectorCompletionChooseCount,
      if_neg hcompletion]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun sectorCompletion => hcompletion ⟨sectorCompletion.1⟩⟩

theorem sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T)
    (hnonempty : Nonempty
      (SixVertexHorizontalSectorCompletion T sector horizontal)) :
    0 < sixVertexHorizontalSectorCompletionChooseCount
      T sector horizontal := by
  rw [← card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    Fintype.card_pos_iff]
  exact hnonempty

theorem sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T)
    (hempty : IsEmpty
      (SixVertexHorizontalSectorCompletion T sector horizontal)) :
    sixVertexHorizontalSectorCompletionChooseCount T sector horizontal = 0 := by
  rw [← card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    Fintype.card_eq_zero_iff]
  exact hempty


theorem card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorConfiguration T left ×
            SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairBigrade pair = grade} =
      ∑ horizontal :
          {horizontal : SixVertexHorizontalField T ×
              SixVertexHorizontalField T //
            sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount
            T left horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T right horizontal.1.2 := by
  rw [card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions]
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  rw [card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    card_sixVertexHorizontalSectorCompletion_eq_chooseCount]


end
end StatMech.FrontierD
