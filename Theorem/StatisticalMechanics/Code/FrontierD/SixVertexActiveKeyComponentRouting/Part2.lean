/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part3


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


attribute [instance]
  SixVertexHorizontalTwoCycleTokenReconnectionComponents.componentFintype


theorem offDiagonalTwoCycleMatching_of_tokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨components⟩ := hroutings grade
  exact components.toSupportedMatching


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_tokenComponentRoutings T middle
        hmiddle_pos hmiddle_lt hroutings)

end
end StatMech.FrontierD
