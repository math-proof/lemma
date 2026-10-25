/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalCoordinate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityMomentumOrderIso
    (lam : Real) (hlam : 0 < lam) :
    Set.Icc (-Real.pi) Real.pi ≃o Set.Icc (-Real.pi) Real.pi := by
  let f : Set.Icc (-Real.pi) Real.pi -> Set.Icc (-Real.pi) Real.pi :=
    fun alpha => ⟨sixVertexRapidityMomentum lam alpha,
      sixVertexRapidityMomentum_mem_Icc hlam alpha.property⟩
  have hfStrict : StrictMono f := by
    intro alpha beta hab
    exact strictMono_sixVertexRapidityMomentum hlam hab
  have hfSurj : Function.Surjective f := by
    intro x
    have hcontinuous : Continuous (sixVertexRapidityMomentum lam) :=
      continuous_iff_continuousAt.2 fun alpha =>
        (hasDerivAt_sixVertexRapidityMomentum hlam alpha).continuousAt
    have hcont : ContinuousOn (sixVertexRapidityMomentum lam)
        (Set.Icc (-Real.pi) Real.pi) :=
      hcontinuous.continuousOn
    have hxRange : (x : Real) ∈ Set.Icc
        (sixVertexRapidityMomentum lam (-Real.pi))
        (sixVertexRapidityMomentum lam Real.pi) := by
      rw [sixVertexRapidityMomentum_neg_pi hlam,
        sixVertexRapidityMomentum_pi hlam]
      exact x.property
    obtain ⟨alpha, halpha, heq⟩ :=
      intermediate_value_Icc neg_pi_le_pi hcont hxRange
    exact ⟨⟨alpha, halpha⟩, Subtype.ext heq⟩
  exact StrictMono.orderIsoOfSurjective f hfStrict hfSurj


def sixVertexMomentumRapidity
    (lam : Real) (hlam : 0 < lam) (x : Real) : Real :=
  ((sixVertexRapidityMomentumOrderIso lam hlam).symm
    (Set.projIcc (-Real.pi) Real.pi neg_pi_le_pi x) : Real)

end
end StatMech.FrontierD
