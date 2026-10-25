/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoOrientedStrandEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexDirectedTorusEdge T :=
  sixVertexDirectedTorusEdgeOfArrow omega
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1)

end
end StatMech.FrontierD
