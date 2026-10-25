/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexHorizontalDegreeTwoLoopRoutedTarget_val
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1 =
      sixVertexLoopDecoratedRoutedUnitTarget middle
        hmiddle_pos hmiddle_lt source.1 key := by
  rfl


theorem sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1 := by
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1.1.1, source.1.1.2.1)
    ((sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1.1.1,
      (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1.2.1)
  have hrelated := key.target_twoCycleFine
  rw [← sixVertexLoopDecoratedRoutedUnitTarget_colored middle
    hmiddle_pos hmiddle_lt source.1 key] at hrelated
  simpa only [sixVertexHorizontalDegreeTwoLoopRoutedTarget_val,
    sixVertexLoopDecoratedPairColored_false_arrows,
    sixVertexLoopDecoratedPairColored_true_arrows] using hrelated


end
end StatMech.FrontierD
