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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusAgreementMask
    {T : EvenTorus} (omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal edge := omega.horizontal edge == eta.horizontal edge
  vertical edge := omega.vertical edge == eta.vertical edge


def sixVertexLocalAgreementMask
    (first second : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern :=
  fun side => first side == second side

end
end StatMech.FrontierD
