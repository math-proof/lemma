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
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part2


namespace StatMech.FrontierD

noncomputable section

section finiteChecks

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    ¬ ((sixVertexArrowsOfFields
        sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexArrowsOfFields
              sixVertexFourByTwoCycleMiddleFirst.horizontal vertical)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoCycleMiddleFirst.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 ->
      vertical = sixVertexFourByTwoCycleMiddleFirst.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoCycleMiddleSecond.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoCycleMiddleSecond.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 ->
      vertical = sixVertexFourByTwoCycleMiddleSecond.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleRepair_bigrade :
    sixVertexHorizontalPairBigrade
        (sixVertexFourByTwoCycleMiddleFirst.horizontal,
          sixVertexFourByTwoCycleMiddleSecond.horizontal) =
      sixVertexFourByTwoActiveObstructionGrade := by
  decide +revert

end finiteChecks

theorem sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty :
    IsEmpty
      (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero
        sixVertexFourByTwoCycleMiddleFirst.horizontal) := by
  constructor
  rintro ⟨⟨vertical, hice⟩, hsector⟩
  exact sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible vertical
    ⟨hice, hsector⟩

end
end StatMech.FrontierD
