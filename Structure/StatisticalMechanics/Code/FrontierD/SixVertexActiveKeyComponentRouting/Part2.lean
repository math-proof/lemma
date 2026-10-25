/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting


namespace StatMech.FrontierD

noncomputable section

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype


structure SixVertexHorizontalTwoCycleActiveKeyComponentRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  route : SixVertexPairFineUnionKey T -> SixVertexPairFineUnionKey T
  active_injective : forall first second,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade first ->
      0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade second ->
      route first = route second -> first = second
  supported : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexPairFineUnionKeyTwoCycleRelated key (route key)
  components : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexHorizontalTwoCycleFiberReconnectionComponents T middle
        hmiddle_pos hmiddle_lt grade key (route key)


end
end StatMech.FrontierD
