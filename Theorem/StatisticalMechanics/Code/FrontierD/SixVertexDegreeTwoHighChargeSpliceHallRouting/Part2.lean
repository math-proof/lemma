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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part2


namespace StatMech.FrontierD

noncomputable section

open Finset

@[simp] theorem sixVertexHorizontalDegreeTwoLoopSpliceTarget_val
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1 =
      sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt
        source.1 key := rfl


theorem sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1 := by
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1.1.1, source.1.1.2.1)
    ((sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1.1.1,
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1.2.1)
  have hrelated := key.target_twoCycleFine
  rw [← sixVertexLoopDecoratedSpliceUnitTarget_colored middle
    hmiddle_pos hmiddle_lt source.1 key] at hrelated
  simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
    sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows] using hrelated


theorem sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    FKColoredFineTwoCycleUnitTransferSpliceKey.SourceSeamDifferenceTwo
      (sixVertexLoopDecoratedPairColored source.1) := by
  unfold FKColoredFineTwoCycleUnitTransferSpliceKey.SourceSeamDifferenceTwo
  rw [sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows]
  have hlower := source.1.1.1.2.2
  have hupper := source.1.1.2.2.2
  simp only [sixVertexHorizontalLowerSector,
    sixVertexHorizontalUpperSector] at hlower hupper
  omega


end
end StatMech.FrontierD
