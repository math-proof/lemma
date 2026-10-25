/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveDart_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree
      (seed.nextPositiveDart hsame) = 1 := by
  classical
  exact (Finset.mem_filter.mp (seed.nextPositiveIndex_mem hsame)).2.2

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.first_ne_nextPositiveDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.first ≠ seed.nextPositiveDart hsame := by
  intro heq
  apply seed.nextPositiveIndex_ne_zero hsame
  apply sixVertexDegreeTwoStrandCycleEnumeration_injective
    homega heta hdegree seed.first
  rw [sixVertexDegreeTwoStrandCycleEnumeration_zero]
  exact heq.symm

end
end StatMech.FrontierD
