/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


def SixVertexHorizontalTwoCycleFiberReconnectionComponents.toEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat} {sourceKey targetKey : SixVertexPairFineUnionKey T}
    (components : SixVertexHorizontalTwoCycleFiberReconnectionComponents
      T middle hmiddle_pos hmiddle_lt grade sourceKey targetKey) :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade sourceKey ↪
      SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade targetKey where
  toFun := components.reconnect
  inj' := by
    intro first second heq
    exact components.injective_within_component first second
      (components.output_recovers_component first second heq) heq


def sixVertexHorizontalTwoCycleFiberReconnectionComponentsOfEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat} {sourceKey targetKey : SixVertexPairFineUnionKey T}
    (embedding :
      SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade sourceKey ↪
        SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade targetKey) :
    SixVertexHorizontalTwoCycleFiberReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade sourceKey targetKey where
  Component := Unit
  componentFintype := inferInstance
  sourceComponent := fun _ => ()
  reconnect := embedding
  output_recovers_component := by simp
  injective_within_component := by
    intro first second _ heq
    exact embedding.injective heq


end
end StatMech.FrontierD
