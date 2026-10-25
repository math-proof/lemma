/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      Nonempty
        (SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
            hmiddle_pos hmiddle_lt grade key ↪
          SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
            hmiddle_pos hmiddle_lt grade key)


end
end StatMech.FrontierD
