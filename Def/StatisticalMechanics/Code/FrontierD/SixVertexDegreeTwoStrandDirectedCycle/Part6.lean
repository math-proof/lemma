/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part5


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoStrandDirectedSimpleCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexDirectedSimpleCycle T :=
  sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration
    homega heta hdegree
    (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))
    (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))
    (sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCycleEnumeration_injective
      homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCycleEnumeration_next
      homega heta hdegree seed)

end
end StatMech.FrontierD
