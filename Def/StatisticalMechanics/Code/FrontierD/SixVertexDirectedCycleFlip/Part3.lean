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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusFlip
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    SixVertexArrows T where
  horizontal edge := if mask.horizontal edge then !omega.horizontal edge
    else omega.horizontal edge
  vertical edge := if mask.vertical edge then !omega.vertical edge
    else omega.vertical edge


def sixVertexTorusMaskXor
    {T : EvenTorus} (first second : SixVertexArrows T) :
    SixVertexArrows T where
  horizontal edge := first.horizontal edge != second.horizontal edge
  vertical edge := first.vertical edge != second.vertical edge


end
end StatMech.FrontierD
