/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalCoordinate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexMomentumRapidity
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexMomentumRapidity lam hlam) := by
  unfold sixVertexMomentumRapidity
  exact continuous_subtype_val.comp
    ((sixVertexRapidityMomentumOrderIso lam hlam).symm.continuous.comp
      continuous_projIcc)

theorem sixVertexMomentumRapidity_rapidityMomentum
    {lam : Real} (hlam : 0 < lam) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexMomentumRapidity lam hlam
        (sixVertexRapidityMomentum lam alpha) = alpha := by
  unfold sixVertexMomentumRapidity
  rw [Set.projIcc_of_mem neg_pi_le_pi
    (sixVertexRapidityMomentum_mem_Icc hlam halpha)]
  exact congrArg Subtype.val
    ((sixVertexRapidityMomentumOrderIso lam hlam).symm_apply_apply
      ⟨alpha, halpha⟩)

theorem sixVertexRapidityMomentum_momentumRapidity
    {lam : Real} (hlam : 0 < lam) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRapidityMomentum lam
      (sixVertexMomentumRapidity lam hlam x) = x := by
  unfold sixVertexMomentumRapidity
  rw [Set.projIcc_of_mem neg_pi_le_pi hx]
  exact congrArg Subtype.val
    ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply ⟨x, hx⟩)


end
end StatMech.FrontierD
