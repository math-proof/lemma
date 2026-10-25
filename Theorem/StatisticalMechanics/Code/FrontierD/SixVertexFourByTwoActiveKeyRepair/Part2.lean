/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero :
    sixVertexHorizontalPairProfileChooseWeight
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoActiveCycleRepairProfile = 0 := by
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
    (sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal)
    sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty

theorem sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos :
    0 < sixVertexHorizontalProfileSurplus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveCycleRepairProfile := by
  rw [sixVertexHorizontalProfileSurplus_eq_sub]
  have hsourceFirst :
      sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
        sixVertexFourByTwoCycleMiddleFirst.horizontal = 0 := by
    exact sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
      _ _ _ sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty
  have htargetFirst :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoCycleMiddleFirst.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveCycleMiddleFirstCompletion⟩
  have htargetSecond :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoCycleMiddleSecond.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveCycleMiddleSecondCompletion⟩
  change 0 <
    sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoCycleMiddleFirst.horizontal,
            sixVertexFourByTwoCycleMiddleSecond.horizontal)) -
      sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoCycleMiddleFirst.horizontal,
            sixVertexFourByTwoCycleMiddleSecond.horizontal))
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile,
    ← sixVertexHorizontalPairChooseWeight_eq_profile]
  simp only [hsourceFirst, zero_mul, Nat.sub_zero]
  positivity

end
end StatMech.FrontierD
