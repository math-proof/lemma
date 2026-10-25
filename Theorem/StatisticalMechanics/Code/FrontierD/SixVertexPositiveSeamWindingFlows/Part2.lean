/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusEdgeSeamSign_eq_one_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {edge : SixVertexTorusEdge T}
    (h : sixVertexTorusEdgeSeamSign omega eta edge = 1) :
    edge.1 = 1 ∧ edge.2.2 = svFinLast T.height_pos := by
  unfold sixVertexTorusEdgeSeamSign at h
  split at h
  · assumption
  · simp at h

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstSeamEdge.1 = 1 ∧
      seed.firstSeamEdge.2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape seed.first_seamSign

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.secondSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.secondSeamEdge.1 = 1 ∧
      seed.secondSeamEdge.2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape seed.second_seamSign


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_secondSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstSeamEdge ≠ seed.secondSeamEdge := by
  intro hedge
  apply seed.distinct
  apply (sixVertexOrientedDisagreementDartEquivEdge homega heta hdegree).injective
  apply Subtype.ext
  exact hedge


end
end StatMech.FrontierD
