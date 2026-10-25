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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part15


namespace StatMech.FrontierD

noncomputable section

open Finset

structure SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighMask : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      SixVertexHorizontalDegreeTwoLoopFullUnitMask source
  decode : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade →
    Option (SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
  decode_high_matching : ∀ source,
    decode (high.pairedMatching source) = some source.1
  decode_nonHigh_target : ∀ source
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source),
    decode (sixVertexHorizontalDegreeTwoLoopSpliceTarget source
      (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source
        (nonHighMask source hnon))) = some source

end
end StatMech.FrontierD
