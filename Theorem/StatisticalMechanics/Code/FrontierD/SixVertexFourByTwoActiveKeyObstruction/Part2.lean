/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveObstructionProfile_deficit_pos :
    0 < sixVertexHorizontalProfileDeficit
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionProfile := by
  rw [sixVertexHorizontalProfileDeficit_eq_sub]
  have hsourceFirst :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
        sixVertexFourByTwoLowArrows.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveLowCompletion⟩
  have hsourceSecond :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoHighArrows.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveHighCompletion⟩
  have htargetSecond :
      sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoHighArrows.horizontal = 0 := by
    exact sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
      _ _ _ sixVertexFourByTwoActiveHighMiddle_isEmpty
  change 0 <
    sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoLowArrows.horizontal,
            sixVertexFourByTwoHighArrows.horizontal)) -
      sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoLowArrows.horizontal,
            sixVertexFourByTwoHighArrows.horizontal))
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile,
    ← sixVertexHorizontalPairChooseWeight_eq_profile]
  simp only [htargetSecond, mul_zero, Nat.sub_zero]
  positivity

end
end StatMech.FrontierD
