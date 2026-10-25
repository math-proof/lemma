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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexRapidityMomentumFamilyEquiv
    {a b : Real} (ha : 2 < a) :
    Continuous (sixVertexRapidityMomentumFamilyEquiv (b := b) ha) := by
  apply Continuous.prodMk continuous_fst
  exact Continuous.subtype_mk
    (continuous_sixVertexRapidityMomentum_family (b := b) ha) _

end
end StatMech.FrontierD
