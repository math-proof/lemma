/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


theorem activeKeyFiberRoutings_of_componentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  exact ⟨routing.toActiveKeyFiberRouting⟩


theorem twoCycleKeyCapacityHall_of_activeKeyComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt :=
  twoCycleKeyCapacityHall_of_activeKeyFiberRoutings T middle
    hmiddle_pos hmiddle_lt
      (activeKeyFiberRoutings_of_componentRoutings T middle
        hmiddle_pos hmiddle_lt hroutings)


end
end StatMech.FrontierD
