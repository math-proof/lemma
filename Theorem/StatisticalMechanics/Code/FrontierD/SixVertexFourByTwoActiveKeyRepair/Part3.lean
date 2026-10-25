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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleFirst.horizontal) :
    completion = sixVertexFourByTwoActiveCycleMiddleFirstCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique vertical
    ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleSecond.horizontal) :
    completion = sixVertexFourByTwoActiveCycleMiddleSecondCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique vertical
    ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveCycleRepairCompletionPair_eq :
    sixVertexHorizontalActualSurplusCompletionPair
        sixVertexFourByTwoActiveCycleRepairSurplusToken =
      (sixVertexFourByTwoActiveCycleMiddleFirstCompletion,
        sixVertexFourByTwoActiveCycleMiddleSecondCompletion) := by
  apply Prod.ext
  · exact sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique _
  · exact sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique _

end
end StatMech.FrontierD
