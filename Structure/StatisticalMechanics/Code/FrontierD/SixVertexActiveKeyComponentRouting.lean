/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalTwoCycleFiberReconnectionComponents
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (sourceKey targetKey : SixVertexPairFineUnionKey T)
    where
  Component : Type
  componentFintype : Fintype Component
  sourceComponent :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
      hmiddle_pos hmiddle_lt grade sourceKey -> Component
  reconnect :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade sourceKey ->
      SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade targetKey
  output_recovers_component : forall first second,
    reconnect first = reconnect second ->
      sourceComponent first = sourceComponent second
  injective_within_component : forall first second,
    sourceComponent first = sourceComponent second ->
      reconnect first = reconnect second -> first = second

end
end StatMech.FrontierD
