/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed.first)) :=
  (sixVertexDegreeTwoStrandPositiveNonzeroIndices
    homega heta hdegree seed.first).min'
      (sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty
        homega heta hdegree seed.first seed.second hsame seed.distinct
        seed.second_seamSign)

end
end StatMech.FrontierD
