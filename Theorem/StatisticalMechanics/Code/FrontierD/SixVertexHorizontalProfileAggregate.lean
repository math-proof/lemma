/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalSectorCompletionChooseCount_eq_profile
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T sector horizontal =
      sixVertexHorizontalProfileChooseCount sector
        (sixVertexHorizontalCompletionProfile T horizontal) := by
  rw [sixVertexHorizontalSectorCompletionChooseCount]
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · rw [if_pos hcompletion]
    simp only [sixVertexHorizontalCompletionProfile, dif_pos hcompletion,
      sixVertexHorizontalProfileChooseCount]
    rw [sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card]
  · rw [if_neg hcompletion]
    rw [sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
    rfl

end
end StatMech.FrontierD
