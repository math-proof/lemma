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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveLowCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoLowArrows.horizontal) :
    completion = sixVertexFourByTwoActiveLowCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveLowCompletion_vertical_unique vertical ⟨hice, hsector⟩

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoHighArrows.horizontal) :
    completion = sixVertexFourByTwoActiveHighCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveHighCompletion_vertical_unique vertical ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveObstructionCompletionPair_eq :
    sixVertexHorizontalActualDeficitCompletionPair sixVertexFourByTwoActiveObstructionToken =
      (sixVertexFourByTwoActiveLowCompletion, sixVertexFourByTwoActiveHighCompletion) := by
  apply Prod.ext
  · exact sixVertexFourByTwoActiveLowCompletion_unique _
  · exact sixVertexFourByTwoActiveHighCompletion_unique _

theorem sixVertexFourByTwoActiveObstructionConfigurationPair_eq :
    (sixVertexHorizontalActualDeficitConfigurationPair
      sixVertexFourByTwoActiveObstructionToken).1 =
      (sixVertexFourByTwoLowConfiguration,
        sixVertexFourByTwoHighConfiguration) := by
  apply Prod.ext
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.1.1.1)
        sixVertexFourByTwoActiveObstructionCompletionPair_eq
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.2.1.1)
        sixVertexFourByTwoActiveObstructionCompletionPair_eq

end
end StatMech.FrontierD
