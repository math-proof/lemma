/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedEvenChargeBetheCandidateNormalized s k) atTop
      (nhds (sixVertexFixedEvenChargeBetheCandidateInfinity s k)) := by
  have hfactors : Tendsto
      (fun c => ∏ j : Fin (s + k + 1), Complex.normSq
        (sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
          (c ^ 2 - 2 : Real)))
      atTop
      (nhds (∏ j : Fin (s + k + 1),
        sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
    exact tendsto_finsetProd Finset.univ fun j _ =>
      tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized s k j
  have hprod : Tendsto
      (fun c => 2 * ∏ j : Fin (s + k + 1), Complex.normSq
        (sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
          (c ^ 2 - 2 : Real)))
      atTop
      (nhds (2 * ∏ j : Fin (s + k + 1),
        sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
    exact (tendsto_const_nhds.mul hfactors : _)
  unfold sixVertexFixedEvenChargeBetheCandidateInfinity
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedEvenChargeBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexFixedEvenChargeBetheEigenvalueValue
    sixVertexSymmetricBetheEigenvalueValue
  simp_rw [sixVertexFixedEvenPositiveBetheRootAt_eq hc,
    Complex.normSq_div, Complex.normSq_eq_norm_sq]
  have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  have hcount : 2 * s + 2 * (k + 1) = 2 * (s + k + 1) := by omega
  rw [hcount, pow_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by nlinarith : 0 < c ^ 2 - 2)]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end
end StatMech.FrontierD
