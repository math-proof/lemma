/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexPositiveHorizontalWindingFamily_horizontalFlow_same
    {T : EvenTorus} (row : Fin T.height) (column : Fin T.width) :
    (sixVertexPositiveHorizontalWindingFamily row).horizontalFlow
      (column, row) = 1 := by
  classical
  simp [sixVertexPositiveHorizontalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexDirectedSimpleCycle.horizontalFlow,
    sixVertexPositiveHorizontalWindingCycle,
    SixVertexDirectedTorusEdge.horizontalFlow]
  rw [Finset.card_eq_one]
  refine ⟨column, ?_⟩
  ext other
  simp [eq_comm]

@[simp] theorem sixVertexPositiveHorizontalWindingFamily_horizontalFlow_other
    {T : EvenTorus} {first second : Fin T.height} (hne : first ≠ second)
    (column : Fin T.width) :
    (sixVertexPositiveHorizontalWindingFamily second).horizontalFlow
      (column, first) = 0 := by
  classical
  simp [sixVertexPositiveHorizontalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexDirectedSimpleCycle.horizontalFlow,
    sixVertexPositiveHorizontalWindingCycle,
    SixVertexDirectedTorusEdge.horizontalFlow, hne]

@[simp] theorem sixVertexPositiveVerticalWindingFamily_verticalFlow_same
    {T : EvenTorus} (column : Fin T.width) (row : Fin T.height) :
    (sixVertexPositiveVerticalWindingFamily column).verticalFlow (column, row) = 1 := by
  classical
  simp [sixVertexPositiveVerticalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexDirectedSimpleCycle.verticalFlow,
    sixVertexPositiveVerticalWindingCycle,
    SixVertexDirectedTorusEdge.verticalFlow]
  rw [Finset.card_eq_one]
  refine ⟨row, ?_⟩
  ext other
  simp [eq_comm]

@[simp] theorem sixVertexPositiveVerticalWindingFamily_verticalFlow_other
    {T : EvenTorus} {first second : Fin T.width} (hne : first ≠ second)
    (row : Fin T.height) :
    (sixVertexPositiveVerticalWindingFamily second).verticalFlow (first, row) = 0 := by
  classical
  simp [sixVertexPositiveVerticalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexDirectedSimpleCycle.verticalFlow,
    sixVertexPositiveVerticalWindingCycle,
    SixVertexDirectedTorusEdge.verticalFlow, hne]


end
end StatMech.FrontierD
