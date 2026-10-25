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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveCycleRepairPhysicalTarget_surplusPreimage :
    ∃ token : SixVertexHorizontalActualSurplusTokens
        sixVertexFourByTwoTorus sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne,
      sixVertexHorizontalActualSurplusConfigurationPair token =
        sixVertexFourByTwoActiveCycleRepairPhysicalTarget := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero

theorem sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq :
    (sixVertexHorizontalActualSurplusConfigurationPair
      sixVertexFourByTwoActiveCycleRepairSurplusToken).1 =
      (sixVertexFourByTwoActiveCycleMiddleFirstConfiguration,
        sixVertexFourByTwoActiveCycleMiddleSecondConfiguration) := by
  apply Prod.ext
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.1.1.1)
        sixVertexFourByTwoActiveCycleRepairCompletionPair_eq
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.2.1.1)
        sixVertexFourByTwoActiveCycleRepairCompletionPair_eq

theorem sixVertexFourByTwoActiveCycleRepairSurplusToken_key :
    sixVertexHorizontalActualSurplusFineUnionKey
        sixVertexFourByTwoActiveCycleRepairSurplusToken =
      sixVertexFourByTwoActiveCycleRepairKey := by
  unfold sixVertexHorizontalActualSurplusFineUnionKey
    sixVertexFourByTwoActiveCycleRepairKey
  exact congrArg
    (fun pair => sixVertexPairFineUnionKey (pair.1.1, pair.2.1))
    sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq

end
end StatMech.FrontierD
