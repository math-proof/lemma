/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part4


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.nextPositiveIndex hsame ∈
      sixVertexDegreeTwoStrandPositiveNonzeroIndices
        homega heta hdegree seed.first :=
  Finset.min'_mem _ _

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.nextPositiveIndex hsame ≠
      sixVertexDegreeTwoStrandCycleZeroIndex
        homega heta hdegree seed.first := by
  classical
  exact (Finset.mem_filter.mp (seed.nextPositiveIndex_mem hsame)).2.1

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_minimal
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed.first)))
    (hi : i ≠ sixVertexDegreeTwoStrandCycleZeroIndex
      homega heta hdegree seed.first)
    (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed.first i) = 1) :
    seed.nextPositiveIndex hsame ≤ i := by
  classical
  apply Finset.min'_le
  simp [sixVertexDegreeTwoStrandPositiveNonzeroIndices, hi, hpositive]


end
end StatMech.FrontierD
