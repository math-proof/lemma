/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem activeKeyFiberRoutings_of_reflexiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hembeddings :
      SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle
        hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  refine ⟨{
    route := id
    active_injective := ?_
    supported := ?_
    fiberEmbedding := ?_ }⟩
  · intro first second hfirst hsecond heq
    exact heq
  · intro key hkey
    exact sixVertexPairFineUnionKeyTwoCycleRelated_refl key
  · intro key hkey
    exact Classical.choice (hembeddings grade key hkey)

theorem twoCycleKeyCapacityHall_of_reflexiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hembeddings :
      SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle
        hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt :=
  twoCycleKeyCapacityHall_of_activeKeyFiberRoutings T middle
    hmiddle_pos hmiddle_lt
      (activeKeyFiberRoutings_of_reflexiveFiberEmbeddings
        T middle hmiddle_pos hmiddle_lt hembeddings)


theorem activeKeyFiberRoutings_of_injectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨route, hinjective, hsupported, hcapacity⟩ := hroutings grade
  refine ⟨{
    route := route
    active_injective := ?_
    supported := ?_
    fiberEmbedding := ?_ }⟩
  · intro first second hfirst hsecond heq
    exact hinjective heq
  · intro key hkey
    exact hsupported key
  · intro key hkey
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
      sixVertexHorizontalActualSurplusFineUnionCapacity] using hcapacity key

end
end StatMech.FrontierD
