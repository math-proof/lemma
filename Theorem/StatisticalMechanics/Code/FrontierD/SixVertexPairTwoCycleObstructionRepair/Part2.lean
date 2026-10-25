/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwo_cycleMiddle_related :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      (sixVertexFourByTwoCycleMiddleFirst,
        sixVertexFourByTwoCycleMiddleSecond) := by
  refine ⟨sixVertexFourByTwoBottomCycleFamily, true, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwo_cycleMiddle_fineProfile :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexFourByTwoLowArrows.horizontal,
          sixVertexFourByTwoHighArrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexFourByTwoCycleMiddleFirst.horizontal,
          sixVertexFourByTwoCycleMiddleSecond.horizontal) := by
  decide +revert

theorem sixVertexFourByTwo_cycleMiddle_fineRelated :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      (sixVertexFourByTwoCycleMiddleFirst,
        sixVertexFourByTwoCycleMiddleSecond) :=
  ⟨sixVertexFourByTwo_cycleMiddle_related,
    sixVertexFourByTwo_cycleMiddle_fineProfile⟩


theorem sixVertexFourByTwo_exists_cycleSupported_middlePair :
    exists alpha beta : SixVertexArrows sixVertexFourByTwoTorus,
      alpha.IceRule /\ beta.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus alpha
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus beta
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexPairAtMostTwoCycleFineRelated
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
        (alpha, beta) := by
  exact ⟨sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleSecond,
    sixVertexFourByTwoCycleMiddleFirst_ice,
    sixVertexFourByTwoCycleMiddleSecond_ice,
    sixVertexFourByTwoCycleMiddleFirst_seamCount,
    sixVertexFourByTwoCycleMiddleSecond_seamCount,
    sixVertexFourByTwo_cycleMiddle_fineRelated⟩


end
end StatMech.FrontierD
