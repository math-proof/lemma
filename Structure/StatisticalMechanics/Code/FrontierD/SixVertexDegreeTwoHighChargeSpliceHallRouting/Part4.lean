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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part10


namespace StatMech.FrontierD

noncomputable section

open Finset

structure SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  layers_ne : ∀ source,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    key.splice.target false ≠ key.splice.target true
  nonHighKey : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredFineTwoCycleUnitTransferSpliceKey
        (sixVertexLoopDecoratedPairColored source.1)
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_target : ∀ source branch,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
      (key.paired
        (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1)
        branch)) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (nonHighKey source hnon)) = some source

end
end StatMech.FrontierD
