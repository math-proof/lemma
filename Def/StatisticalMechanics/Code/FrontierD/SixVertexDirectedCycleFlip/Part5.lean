module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
