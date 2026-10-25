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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part2


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets

noncomputable def toSingleTargets
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade where
  single := decoded.single
  layers_ne := decoded.layers_ne
  base_injective := by
    intro first second heq
    have hdecode := congrArg decoded.decode heq
    have hfirst : decoded.decode
        (sixVertexHorizontalDegreeTwoLoopSpliceTarget first.1
          (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
            T middle hmiddle_pos hmiddle_lt grade decoded.single first)) =
        some first := by
      simpa [FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
        decoded.decode_target first false
    have hsecond : decoded.decode
        (sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1
          (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
            T middle hmiddle_pos hmiddle_lt grade decoded.single second)) =
        some second := by
      simpa [FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
        decoded.decode_target second false
    rw [hfirst, hsecond] at hdecode
    exact Option.some.inj hdecode

end SixVertexHorizontalDegreeTwoLoopDecodedSingleTargets
end
end StatMech.FrontierD
