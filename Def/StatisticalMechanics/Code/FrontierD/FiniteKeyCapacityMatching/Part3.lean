/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalTwoCycleExpandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, exists matching :
      FiniteKeyCapacityCopies (SixVertexPairFineUnionKey T)
          (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade) ->
        FiniteKeyCapacityCopies (SixVertexPairFineUnionKey T)
          (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade),
    Function.Injective matching ∧
      forall source,
        SixVertexPairFineUnionKeyTwoCycleRelated
          source.1 (matching source).1


end
end StatMech.FrontierD
