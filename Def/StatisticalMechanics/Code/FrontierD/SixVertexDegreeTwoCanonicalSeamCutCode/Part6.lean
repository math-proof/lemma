/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part5


namespace StatMech.FrontierD

noncomputable section

def SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalSameStrandCutCode
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    SixVertexCanonicalSameStrandCutCode T where
  arcs := seed.sameStrandArcPair hsame
  firstSeamEdge := seed.firstSeamEdge
  secondSeamEdge := seed.nextPositiveSeamEdge hsame
  first_shape := seed.firstSeamEdge_shape
  second_shape := seed.nextPositiveSeamEdge_shape hsame
  seam_ne := seed.firstSeamEdge_ne_nextPositiveSeamEdge hsame
  first_marked := seed.sameStrandArcPair_first_physical hsame
  second_marked := seed.sameStrandArcPair_second_physical hsame

end
end StatMech.FrontierD
