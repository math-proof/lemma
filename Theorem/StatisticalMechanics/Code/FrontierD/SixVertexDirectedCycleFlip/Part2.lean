/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLocalFlipMask_ice_of_balanced
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
    (sixVertexLocalFlipMask pattern mask).Ice := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalFlipMask] at *
  decide +revert


theorem SixVertexLocalBalancedFlipMask.after_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (hbalanced : SixVertexLocalBalancedFlipMask pattern mask) :
    SixVertexLocalBalancedFlipMask
      (sixVertexLocalFlipMask pattern mask) mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalFlipMask] at *
  decide +revert


theorem sixVertexLocalBalancedFlipMask_of_ice_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hflip : (sixVertexLocalFlipMask pattern mask).Ice) :
    SixVertexLocalBalancedFlipMask pattern mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalFlipMask] at *
  decide +revert


theorem sixVertexLocalBalancedFlipMask_of_cycle
    (pattern mask : SixVertexLocalIncomingPattern)
    (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/
      (sixVertexLocalSwitchMaskCount mask = 2 /\
        sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
    SixVertexLocalBalancedFlipMask pattern mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount] at *
  decide +revert


end
end StatMech.FrontierD
