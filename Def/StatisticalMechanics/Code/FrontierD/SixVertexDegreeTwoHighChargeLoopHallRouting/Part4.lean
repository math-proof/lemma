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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeSeed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :=
  sixVertexDegreeTwoSynchronizedHighChargeSeed
    source.1.1.1.1.2.1 source.1.1.1.2.2.1
    (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source)
    (sixVertexHorizontalDegreeTwoLoopHighChargeComponent source)
    (sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge source)


noncomputable def sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).occurrenceEquiv


noncomputable def sixVertexHorizontalDegreeTwoLoopRoutedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade := by
  let profile := sixVertexHorizontalPairBoundedFineRowProfile
    ((sixVertexLoopDecoratedPairColored source.1 false).arrows.horizontal,
      (sixVertexLoopDecoratedPairColored source.1 true).arrows.horizontal)
  let fineSource : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile :=
    ⟨source.1, by
      simp only [profile, sixVertexLoopDecoratedPairColored_false_arrows,
        sixVertexLoopDecoratedPairColored_true_arrows]⟩
  let target := sixVertexLoopDecoratedRoutedUnitTarget middle
    hmiddle_pos hmiddle_lt source.1 key
  refine ⟨target, ?_⟩
  have hbig := sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade
    middle hmiddle_pos hmiddle_lt profile fineSource key
  exact hbig.trans source.2

end
end StatMech.FrontierD
