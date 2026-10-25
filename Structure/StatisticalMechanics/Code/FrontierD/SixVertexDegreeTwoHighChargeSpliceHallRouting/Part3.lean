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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part8


namespace StatMech.FrontierD

noncomputable section

open Finset

structure SixVertexHorizontalDegreeTwoLoopSpliceReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  high : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    T middle hmiddle_pos hmiddle_lt grade
  nonHighKey : ∀ (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade),
    ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source →
      FKColoredFineTwoCycleUnitTransferSpliceKey
        (sixVertexLoopDecoratedPairColored source.1)
  nonHigh_injective : ∀ first
      (hfirst : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge first) second
      (hsecond : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge second),
    sixVertexHorizontalDegreeTwoLoopSpliceTarget first
        (nonHighKey first hfirst) =
      sixVertexHorizontalDegreeTwoLoopSpliceTarget second
        (nonHighKey second hsecond) →
    first = second
  high_nonHigh_disjoint : ∀
      (highSource : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade)
      (nonHighSource : SixVertexHorizontalDegreeTwoLoopHallSource T middle
        hmiddle_pos hmiddle_lt grade)
      (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge nonHighSource),
    high.pairedMatching highSource ≠
      sixVertexHorizontalDegreeTwoLoopSpliceTarget nonHighSource
        (nonHighKey nonHighSource hnon)

end
end StatMech.FrontierD
