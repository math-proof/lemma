/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem SixVertexAtMostTwoCycleFamily.singletonCycle_horizontalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).horizontalFlow base =
      cycle.horizontalFlow base := by
  simp [SixVertexAtMostTwoCycleFamily.singletonCycle,
    SixVertexAtMostTwoCycleFamily.horizontalFlow]

@[simp] theorem SixVertexAtMostTwoCycleFamily.singletonCycle_verticalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).verticalFlow base =
      cycle.verticalFlow base := by
  simp [SixVertexAtMostTwoCycleFamily.singletonCycle,
    SixVertexAtMostTwoCycleFamily.verticalFlow]


theorem SixVertexDirectedSimpleCycle.flip_first_pair_related
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T) (hfollows : cycle.Follows omega) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (sixVertexTorusFlip cycle.mask omega, eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.singletonCycle cycle, false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [cycle.flip_horizontal_toNat omega hfollows]
    simp
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [cycle.flip_vertical_toNat omega hfollows]
    simp


theorem SixVertexDirectedSimpleCycle.flip_second_pair_related
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T) (hfollows : cycle.Follows eta) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (omega, sixVertexTorusFlip cycle.mask eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.singletonCycle cycle, false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [cycle.flip_horizontal_toNat eta hfollows]
    simp
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [cycle.flip_vertical_toNat eta hfollows]
    simp


end
end StatMech.FrontierD
