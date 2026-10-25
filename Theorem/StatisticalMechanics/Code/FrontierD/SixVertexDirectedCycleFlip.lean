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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLocalFlipMask_ice
    (pattern mask : SixVertexLocalIncomingPattern)
    (hice : pattern.Ice)
    (hmask : sixVertexLocalSwitchMaskCount mask = 0 \/
      (sixVertexLocalSwitchMaskCount mask = 2 /\
        sixVertexLocalSelectedIncomingCount pattern mask = 1)) :
    (sixVertexLocalFlipMask pattern mask).Ice := by
  decide +revert


theorem sixVertexLocalSelectedIncomingCount_flip
    (pattern mask : SixVertexLocalIncomingPattern)
    (htwo : sixVertexLocalSwitchMaskCount mask = 2)
    (hone : sixVertexLocalSelectedIncomingCount pattern mask = 1) :
    sixVertexLocalSelectedIncomingCount
        (sixVertexLocalFlipMask pattern mask) mask = 1 := by
  decide +revert


end
end StatMech.FrontierD
