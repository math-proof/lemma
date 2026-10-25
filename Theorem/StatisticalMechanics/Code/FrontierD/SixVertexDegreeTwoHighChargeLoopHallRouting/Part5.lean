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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets

theorem routedKey_target
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    (targets.routedKey source branch).splice.target =
      ((targets.paired source).key branch).splice.target := by
  exact sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target
    source.1.1 (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
      ((targets.paired source).key branch)


theorem routedTarget_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source false) ≠
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source true) := by
  intro heq
  apply (targets.paired source).key_target_distinct
  have hval := congrArg Subtype.val heq
  have hdecorated :
      sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt
          source.1.1 (targets.routedKey source false) =
        sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt
          source.1.1 (targets.routedKey source true) := by
    simpa only [sixVertexHorizontalDegreeTwoLoopRoutedTarget_val] using hval
  have hcolored := congrArg sixVertexLoopDecoratedPairColored hdecorated
  rw [sixVertexLoopDecoratedRoutedUnitTarget_colored,
    sixVertexLoopDecoratedRoutedUnitTarget_colored,
    targets.routedKey_target source false,
    targets.routedKey_target source true] at hcolored
  exact hcolored


theorem routedTarget_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
      T middle hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    Function.Injective (fun source :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade =>
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (targets.routedKey source branch)) := by
  intro first second heq
  exact targets.source_recoverable first branch second branch heq

end SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets
end
end StatMech.FrontierD
