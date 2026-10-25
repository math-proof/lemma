/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedOddPairScale :
    Tendsto (fun c : Real => c ^ 2 - 2) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 <= c := le_trans (le_max_left _ _) hc
    have hcb : b <= c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-2) hsq)

theorem sixVertexThetaLeftDerivAtZero_add_one_eq
    {c y : Real} (hc : 2 < c) :
    sixVertexThetaLeftDerivAtZero c y + 1 =
      2 * (c ^ 2 + Real.cos y - 1) /
        ((c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2) := by
  have ha : 0 < c ^ 2 + Real.cos y - 1 := by
    nlinarith [Real.neg_one_le_cos y]
  have hden' :
      (c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2 ≠ 0 := by
    positivity
  unfold sixVertexThetaLeftDerivAtZero sixVertexBetheIntegratingFactor
    sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    sixVertexDelta
  rw [Real.cos_zero, Real.sin_zero, zero_sub]
  rw [show 2 * ((2 - c ^ 2) / 2) = 2 - c ^ 2 by ring, neg_sq]
  have hdeneq :
      (1 + Real.cos y - (2 - c ^ 2)) ^ 2 + Real.sin y ^ 2 =
        (c ^ 2 + Real.cos y - 1) ^ 2 + Real.sin y ^ 2 := by ring
  rw [hdeneq]
  field_simp [hden']
  nlinarith [Real.sin_sq_add_cos_sq y]


theorem tendsto_sixVertexThetaLeftDerivAtZero_atTop
    (y : Real -> Real) :
    Tendsto (fun c => sixVertexThetaLeftDerivAtZero c (y c))
      atTop (nhds (-1)) := by
  have hbound : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
      atTop (nhds 0) :=
    tendsto_sixVertexFixedOddPairScale.const_div_atTop 2
  have hadd : Tendsto
      (fun c => sixVertexThetaLeftDerivAtZero c (y c) + 1)
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero'
      (Filter.Eventually.of_forall (fun c => norm_nonneg _)) ?_ hbound
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    change ‖sixVertexThetaLeftDerivAtZero c (y c) + 1‖ <=
      2 / (c ^ 2 - 2)
    rw [Real.norm_eq_abs,
      sixVertexThetaLeftDerivAtZero_add_one_eq hc]
    let a := c ^ 2 + Real.cos (y c) - 1
    let d := c ^ 2 - 2
    have hd : 0 < d := by dsimp [d]; nlinarith
    have hda : d <= a := by
      dsimp [d, a]
      linarith [Real.neg_one_le_cos (y c)]
    have ha : 0 < a := hd.trans_le hda
    have hD : 0 < a ^ 2 + Real.sin (y c) ^ 2 := by positivity
    have hnonneg : 0 <= 2 * a /
        (a ^ 2 + Real.sin (y c) ^ 2) := div_nonneg (by positivity) hD.le
    rw [abs_of_nonneg hnonneg]
    rw [div_le_div_iff₀ hD hd]
    have had : a * d <= a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hda ha.le]
    nlinarith [sq_nonneg (Real.sin (y c))]
  have h := hadd.sub (tendsto_const_nhds :
    Tendsto (fun _ : Real => (1 : Real)) atTop (nhds 1))
  simpa only [add_sub_cancel_right, zero_sub] using h


theorem sixVertexFixedOddCentralLimitingRoot_eq_zero (s k : Nat) :
    sixVertexFixedChargeLimitingRoot (2 * s + 1) k
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
  unfold sixVertexFixedChargeLimitingRoot
  have hn : sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
      2 * (s + k + 1) + 1 := by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hq : sixVertexCentralQuantumNumber
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
    rw [sixVertexCentralQuantumNumber_eq]
    unfold sixVertexFixedChargeBetheCentralIndex
    change (((sixVertexFixedChargeBetheParticleCount (2 * s + 1) k / 2 : Nat) :
      Real) -
      ((sixVertexFixedChargeBetheParticleCount (2 * s + 1) k : Real) - 1) /
        2) = 0
    rw [hn]
    rw [show (2 * (s + k + 1) + 1) / 2 = s + k + 1 by omega]
    push_cast
    ring
  rw [hq]
  simp

theorem sixVertexFixedOddCentralLimitingPhase_eq_one (s k : Nat) :
    sixVertexFixedChargeLimitingPhase (2 * s + 1) k
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 1 := by
  unfold sixVertexFixedChargeLimitingPhase
  rw [sixVertexFixedOddCentralLimitingRoot_eq_zero]
  simp [sixVertexBethePhase]

theorem sixVertexFixedOddLimitingPhase_ne_one_of_ne_central
    (s k : Nat) (j : Fin
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k))
    (hj : j ≠ sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) :
    sixVertexFixedChargeLimitingPhase (2 * s + 1) k j ≠ 1 := by
  intro h
  have heq : sixVertexFixedChargeLimitingPhase (2 * s + 1) k j =
      sixVertexFixedChargeLimitingPhase (2 * s + 1) k
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) := by
    rw [sixVertexFixedOddCentralLimitingPhase_eq_one]
    exact h
  exact hj (sixVertexFixedChargeLimitingPhase_injective
    (2 * s + 1) k heq)


end
end StatMech.FrontierD
