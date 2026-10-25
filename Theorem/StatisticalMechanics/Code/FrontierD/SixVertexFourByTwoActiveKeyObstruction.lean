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
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction
open Finset


namespace StatMech.FrontierD

noncomputable section

section finiteChecks

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighMiddle_impossible
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    ¬ ((sixVertexArrowsOfFields
        sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexArrowsOfFields
              sixVertexFourByTwoHighArrows.horizontal vertical)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveLowCompletion_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoLowArrows.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoLowArrows.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 ->
      vertical = sixVertexFourByTwoLowArrows.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighCompletion_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoHighArrows.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 ->
      vertical = sixVertexFourByTwoHighArrows.vertical := by
  decide +revert

end finiteChecks

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighMiddle_isEmpty :
    IsEmpty
      (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne
        sixVertexFourByTwoHighArrows.horizontal) := by
  constructor
  rintro ⟨⟨vertical, hice⟩, hsector⟩
  exact sixVertexFourByTwoActiveHighMiddle_impossible vertical ⟨hice, hsector⟩

end
end StatMech.FrontierD
