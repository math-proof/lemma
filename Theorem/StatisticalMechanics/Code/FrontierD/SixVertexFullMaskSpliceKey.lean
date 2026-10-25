/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFullUnitMaskSplice_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (sixVertexFullUnitMaskSplice source mask hmask).target =
      sixVertexFullDisagreementColoredTarget source mask hmask := by
  unfold sixVertexFullUnitMaskSplice
  apply FKColoredStrandSplice.ofColorEquiv_target

theorem sixVertexFullUnitMaskSplice_preservesTotalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (sixVertexFullUnitMaskSplice source mask hmask).PreservesTotalC := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← splice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount,
    sixVertexFullUnitMaskSplice_target]
  exact congrArg Prod.fst
    (sixVertexFullDisagreementColoredTarget_bigrade source mask hmask)

theorem sixVertexFullUnitMaskSplice_seamDelta_false
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSplice source mask hmask).seamDelta false = 1 := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  have hsplice := splice.target_upCount false
  rw [sixVertexFullUnitMaskSplice_target,
    sixVertexFullDisagreementColoredTarget_arrows] at hsplice
  simp only [Bool.false_eq_true, if_false] at hsplice
  have hswitch := intCast_upCount_switchFirst_eq_add_seamTransfer
    mask (source false).arrows (source true).arrows
  rw [htransfer] at hswitch
  rw [hswitch] at hsplice
  change splice.seamDelta false = 1
  omega

theorem sixVertexFullUnitMaskSplice_seamDelta_true
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSplice source mask hmask).seamDelta true = -1 := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  have hsplice := splice.target_upCount true
  rw [sixVertexFullUnitMaskSplice_target,
    sixVertexFullDisagreementColoredTarget_arrows] at hsplice
  simp only [if_true] at hsplice
  have hswitch := intCast_upCount_switchSecond_eq_sub_seamTransfer
    mask (source false).arrows (source true).arrows
  rw [htransfer] at hswitch
  rw [hswitch] at hsplice
  change splice.seamDelta true = -1
  omega


end
end StatMech.FrontierD
