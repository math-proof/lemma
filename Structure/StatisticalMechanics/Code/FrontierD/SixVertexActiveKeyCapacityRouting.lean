/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalTwoCycleActiveKeyFiberRouting
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
  fiberEmbedding : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade key ↪
        SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade (route key)


end
end StatMech.FrontierD
