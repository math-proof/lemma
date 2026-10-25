/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part3


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoExceptionalFlat_fineRelated (i : Fin 4) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceFlatArrows
        (sixVertexFourByTwoExceptionalRepairFlatIndex i))
      (sixVertexFourByTwoTargetFlatArrows
        (sixVertexFourByTwoExceptionalRepairFlatIndex i)) := by
  fin_cases i
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 0,
        sixVertexFourByTwoExceptionalSourceSecond 0)
      (sixVertexFourByTwoExceptionalTargetFirst 0,
        sixVertexFourByTwoExceptionalTargetSecond 0)
    exact sixVertexFourByTwoExceptional_fineRelated 0
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 1,
        sixVertexFourByTwoExceptionalSourceSecond 1)
      (sixVertexFourByTwoExceptionalTargetFirst 1,
        sixVertexFourByTwoExceptionalTargetSecond 1)
    exact sixVertexFourByTwoExceptional_fineRelated 1
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 2,
        sixVertexFourByTwoExceptionalSourceSecond 2)
      (sixVertexFourByTwoExceptionalTargetFirst 2,
        sixVertexFourByTwoExceptionalTargetSecond 2)
    exact sixVertexFourByTwoExceptional_fineRelated 2
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 3,
        sixVertexFourByTwoExceptionalSourceSecond 3)
      (sixVertexFourByTwoExceptionalTargetFirst 3,
        sixVertexFourByTwoExceptionalTargetSecond 3)
    exact sixVertexFourByTwoExceptional_fineRelated 3


theorem sixVertexFourByTwoMatchingTable_fineRelated (i : Fin 200) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceFlatArrows i)
      (sixVertexFourByTwoTargetFlatArrows i) := by
  by_cases hordinary : ¬ sixVertexFourByTwoExceptionalFlatIndex i
  · obtain ⟨hhorizontal, hvertical, hfine⟩ :=
      sixVertexFourByTwoOrdinaryFlat_fineUnion i hordinary
    exact ⟨sixVertexPairAtMostTwoCycleRelated_of_union_eq
      hhorizontal hvertical, hfine⟩
  · have hexceptional := Classical.not_not.mp hordinary
    rcases hexceptional with h20 | h29 | h170 | h179
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 0 := by
        apply Fin.ext
        exact h20
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 0
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 2 := by
        apply Fin.ext
        exact h29
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 2
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 1 := by
        apply Fin.ext
        exact h170
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 1
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 3 := by
        apply Fin.ext
        exact h179
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 3

end
end StatMech.FrontierD
