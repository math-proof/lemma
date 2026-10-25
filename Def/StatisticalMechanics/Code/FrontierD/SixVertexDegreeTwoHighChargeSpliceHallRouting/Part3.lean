/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part2


namespace StatMech.FrontierD

noncomputable section

open Finset

noncomputable def sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat)
    (single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
      SixVertexDegreeTwoSynchronizedSupportedSplitTarget
        (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source))
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1.1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration source.1.1
      (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
      (single source).toFineRoutedKey)


end
end StatMech.FrontierD
