/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPairAtMostTwoCycleFineRelated_swap_target
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated source (target.2, target.1) := by
  rcases target with ⟨targetFirst, targetSecond⟩
  rcases hrelated.1 with ⟨family, sign, hhorizontal, hvertical⟩
  constructor
  · refine ⟨family, sign, ?_, ?_⟩
    · rw [show sixVertexPairUnionHorizontalDelta source
          (targetSecond, targetFirst) =
          sixVertexPairUnionHorizontalDelta source
            (targetFirst, targetSecond) by
        funext v
        simp only [sixVertexPairUnionHorizontalDelta,
          sixVertexPairUnionHorizontal]
        omega]
      exact hhorizontal
    · rw [show sixVertexPairUnionVerticalDelta source
          (targetSecond, targetFirst) =
          sixVertexPairUnionVerticalDelta source
            (targetFirst, targetSecond) by
        funext v
        simp only [sixVertexPairUnionVerticalDelta,
          sixVertexPairUnionVertical]
        omega]
      exact hvertical
  · calc
      sixVertexHorizontalPairBoundedFineRowProfile
          (source.1.horizontal, source.2.horizontal) =
          sixVertexHorizontalPairBoundedFineRowProfile
            (targetFirst.horizontal, targetSecond.horizontal) := hrelated.2
      _ = sixVertexHorizontalPairBoundedFineRowProfile
            (targetSecond.horizontal, targetFirst.horizontal) :=
        (sixVertexSwapHorizontalLayers_boundedFineRowProfile
          (targetFirst.horizontal, targetSecond.horizontal)).symm


end
end StatMech.FrontierD
