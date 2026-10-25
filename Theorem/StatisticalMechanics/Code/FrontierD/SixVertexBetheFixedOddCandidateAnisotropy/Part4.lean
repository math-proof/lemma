/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedOddChargeBetheCandidateNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeBetheCandidateNormalized s k) atTop
      (nhds (sixVertexFixedOddChargeBetheCandidateInfinity s k)) := by
  have hprod :=
    (tendsto_sixVertexFixedOddChargeBethePrefactorNormalized s k).mul
      (tendsto_sixVertexFixedOddChargeNormalizedMProduct s k)
  unfold sixVertexFixedOddChargeBetheCandidateInfinity
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedOddChargeBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexFixedOddChargeBetheEigenvalueValue
    sixVertexZeroPhaseBetheEigenvalueValue
    sixVertexFixedOddChargeBethePrefactorNormalized
    sixVertexFixedOddChargeNormalizedMProduct
  rw [dif_pos hc]
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc, norm_div]
  have hdpos : 0 < c ^ 2 - 2 := by nlinarith
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  have hn : 0 < sixVertexFixedChargeBetheParticleCount (2 * s + 1) k :=
    sixVertexFixedChargeBetheParticleCount_pos _ _
  have hpow : (c ^ 2 - 2) *
      (c ^ 2 - 2) ^
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k - 1) =
      (c ^ 2 - 2) ^
        sixVertexFixedChargeBetheParticleCount (2 * s + 1) k := by
    rw [← pow_succ']
    congr
    omega
  rw [← hpow]
  field_simp [hdpos.ne']

end
end StatMech.FrontierD
