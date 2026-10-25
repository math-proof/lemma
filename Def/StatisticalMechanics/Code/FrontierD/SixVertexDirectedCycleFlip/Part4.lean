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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part3


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedCycleFlipMask
    {T : EvenTorus} (omega mask : SixVertexArrows T) : Prop :=
  forall v,
    sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask mask v) = 0 \/
      (sixVertexLocalSwitchMaskCount
            (sixVertexTorusLocalSwitchMask mask v) = 2 /\
        sixVertexLocalSelectedIncomingCount
            (sixVertexLocalIncomingPattern omega v)
            (sixVertexTorusLocalSwitchMask mask v) = 1)


def SixVertexBalancedFlipMask
    {T : EvenTorus} (omega mask : SixVertexArrows T) : Prop :=
  forall v, SixVertexLocalBalancedFlipMask
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)

end
end StatMech.FrontierD
