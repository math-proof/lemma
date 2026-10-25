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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip


namespace StatMech.FrontierD

noncomputable section

def SixVertexLocalBalancedFlipMask
    (pattern mask : SixVertexLocalIncomingPattern) : Prop :=
  2 * sixVertexLocalSelectedIncomingCount pattern mask =
    sixVertexLocalSwitchMaskCount mask


end
end StatMech.FrontierD
