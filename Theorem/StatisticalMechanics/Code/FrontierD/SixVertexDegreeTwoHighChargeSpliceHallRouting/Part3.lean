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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part4


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets

theorem branchKey_true_target
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    (targets.branchKey source true).splice.target =
      fkColoredLoopPairingPairSwapLayers
        (targets.branchKey source false).splice.target := by
  simp [branchKey, FKColoredFineTwoCycleUnitTransferSpliceKey.paired]


theorem target_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source false) ≠
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source true) := by
  intro heq
  apply (targets.key source).paired_target_distinct
    (sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source.1)
    (targets.layers_ne source)
  have hval := congrArg Subtype.val heq
  have hcolored := congrArg sixVertexLoopDecoratedPairColored hval
  simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
    sixVertexLoopDecoratedSpliceUnitTarget_colored] using hcolored


theorem target_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    Function.Injective (fun source :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
        (targets.branchKey source branch)) := by
  cases branch
  · simpa [branchKey, key,
      FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using
      targets.base_injective
  · intro first second heq
    apply targets.base_injective
    apply Subtype.ext
    apply sixVertexLoopDecoratedPairColored_injective
    have hcolored := congrArg sixVertexLoopDecoratedPairColored
      (congrArg Subtype.val heq)
    have hbranch : (targets.branchKey first true).splice.target =
        (targets.branchKey second true).splice.target := by
      simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
        sixVertexLoopDecoratedSpliceUnitTarget_colored] using hcolored
    rw [targets.branchKey_true_target first,
      targets.branchKey_true_target second] at hbranch
    have horiginal := congrArg fkColoredLoopPairingPairSwapLayers hbranch
    simpa [branchKey, key,
      FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using horiginal


end SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
end
end StatMech.FrontierD
