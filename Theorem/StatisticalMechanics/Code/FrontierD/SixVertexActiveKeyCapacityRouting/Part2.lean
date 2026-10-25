/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem twoCycleKeyCapacityHall_of_activeKeyFiberRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  apply finiteKeyCapacityHall_of_activeInjectiveRouting
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated routing.route
  · exact routing.active_injective
  · exact routing.supported
  · intro key hkey
    simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
      sixVertexHorizontalActualSurplusFineUnionCapacity] using
      Fintype.card_le_of_embedding (routing.fiberEmbedding key hkey)


end
end StatMech.FrontierD
