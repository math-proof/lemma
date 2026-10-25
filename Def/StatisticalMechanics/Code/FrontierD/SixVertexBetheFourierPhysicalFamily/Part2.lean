/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Mathlib.Topology.Homeomorph.Lemmas
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityMomentumFamilyHomeomorph
    {a b : Real} (ha : 2 < a) :
    (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) ≃ₜ
      (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) :=
  (sixVertexRapidityMomentumFamilyEquiv (b := b) ha).toHomeomorphOfContinuousClosed
    (continuous_sixVertexRapidityMomentumFamilyEquiv (b := b) ha)
    (continuous_sixVertexRapidityMomentumFamilyEquiv (b := b) ha).isClosedMap

def sixVertexMomentumRapidityFamily
    {a b : Real} (ha : 2 < a)
    (z : Set.Icc a b × Real) : Real :=
  ((sixVertexRapidityMomentumFamilyHomeomorph (b := b) ha).symm
    (z.1, Set.projIcc (-Real.pi) Real.pi neg_pi_le_pi z.2)).2.1

end
end StatMech.FrontierD
