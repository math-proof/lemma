/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part2


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    (seed.nextPositiveSeamEdge hsame).1 = 1 ∧
      (seed.nextPositiveSeamEdge hsame).2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape
    (seed.nextPositiveDart_seamSign hsame)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_nextPositiveSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.firstSeamEdge ≠ seed.nextPositiveSeamEdge hsame := by
  intro hedge
  apply seed.first_ne_nextPositiveDart hsame
  apply (sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree).injective
  apply Subtype.ext
  exact hedge


end
end StatMech.FrontierD
