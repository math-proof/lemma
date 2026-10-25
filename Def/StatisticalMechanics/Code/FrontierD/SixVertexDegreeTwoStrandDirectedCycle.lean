/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation


namespace StatMech.FrontierD

noncomputable section

def sixVertexDirectedTorusEdgeOfArrow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) : SixVertexDirectedTorusEdge T :=
  if edge.1 = 0 then
    .horizontal edge.2 (omega.horizontal edge.2)
  else .vertical edge.2 (omega.vertical edge.2)

end
end StatMech.FrontierD
