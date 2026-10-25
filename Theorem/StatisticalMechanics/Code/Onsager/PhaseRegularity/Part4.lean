/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part4


namespace StatMech.Onsager

theorem ons_noncriticalGap_pos {beta : ℝ} (hbeta : 0 < beta)
    (hcrit : beta ≠ ons_betaC) :
    0 < ons_noncriticalGap beta := by
  have hsne : Real.sinh (2 * beta) ≠ 1 := by
    intro hs
    exact hcrit ((ons_betaC_unique beta hbeta).mp hs)
  exact abs_pos.mpr (sub_ne_zero.mpr hsne)

theorem ons_noncriticalNeighborhood_mem_nhds {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_noncriticalNeighborhood beta ∈ nhds beta := by
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcosh : Continuous (fun b : ℝ => Real.cosh (2 * b)) :=
    Real.continuous_cosh.comp hlin
  have hpos : ∀ᶠ b : ℝ in nhds beta, 0 < b := eventually_gt_nhds hbeta
  have hgapEv : ∀ᶠ b : ℝ in nhds beta,
      ons_noncriticalGap beta / 2 < |Real.sinh (2 * b) - 1| := by
    apply continuousAt_const.eventually_lt ((hsinh.sub continuous_const).abs.continuousAt)
    change ons_noncriticalGap beta / 2 < ons_noncriticalGap beta
    linarith
  have hcoshEv : ∀ᶠ b : ℝ in nhds beta,
      |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 := by
    apply hcosh.abs.continuousAt.eventually_lt continuousAt_const
    linarith
  have hsinhEv : ∀ᶠ b : ℝ in nhds beta,
      |Real.sinh (2 * b)| < |Real.sinh (2 * beta)| + 1 := by
    apply hsinh.abs.continuousAt.eventually_lt continuousAt_const
    linarith
  filter_upwards [hpos, hgapEv, hcoshEv, hsinhEv] with b hb hbg hbc hbs
  exact ⟨hb, hbg, hbc, hbs⟩

theorem ons_gInt_uniform_lower_noncritical {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    (ons_noncriticalGap beta / 2) ^ 2 ≤ ons_gInt b k1 k2 := by
  have hsinh0 : 0 ≤ Real.sinh (2 * b) := by
    rw [Real.sinh_nonneg_iff]
    linarith [hb.1]
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  have habs := hb.2.1
  have hsq : (ons_noncriticalGap beta / 2) ^ 2 ≤
      (Real.sinh (2 * b) - 1) ^ 2 := by
    nlinarith [sq_abs (Real.sinh (2 * b) - 1)]
  nlinarith [mul_nonneg hsinh0 hA]

theorem ons_gInt_pos_noncriticalNeighborhood {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    0 < ons_gInt b k1 k2 := by
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  exact lt_of_lt_of_le (sq_pos_of_pos (div_pos hgap0 two_pos))
    (ons_gInt_uniform_lower_noncritical hbeta hcrit hb)


theorem ons_logGIntBetaDeriv_abs_le_noncritical {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    |ons_logGIntBetaDeriv b k1 k2| ≤
      (2 * (|Real.cosh (2 * beta)| + 1) *
          (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
        (ons_noncriticalGap beta / 2) ^ 2 := by
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  have hden := ons_gInt_uniform_lower_noncritical (k1 := k1) (k2 := k2) hbeta hcrit hb
  have hdenpos := ons_gInt_pos_noncriticalNeighborhood (k1 := k1) (k2 := k2) hbeta hcrit hb
  have hcosh : |Real.cosh (2 * b)| ≤ |Real.cosh (2 * beta)| + 1 := hb.2.2.1.le
  have hsinh : |Real.sinh (2 * b)| ≤ |Real.sinh (2 * beta)| + 1 := hb.2.2.2.le
  have hinner :
      |2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2| ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
    calc
      |2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2| ≤
          |2 * Real.sinh (2 * b)| + |Real.cos k1| + |Real.cos k2| := by
            linarith [abs_sub (2 * Real.sinh (2 * b) - Real.cos k1) (Real.cos k2),
              abs_sub (2 * Real.sinh (2 * b)) (Real.cos k1)]
      _ ≤ 2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
        rw [abs_mul]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  have hnum : |ons_gIntBetaDeriv b k1 k2| ≤
      2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by
    rw [ons_gIntBetaDeriv, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hcnonneg : 0 ≤ |Real.cosh (2 * beta)| + 1 := by positivity
    have hinnonneg : 0 ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by positivity
    nlinarith [mul_le_mul hcosh hinner (abs_nonneg _) hcnonneg]
  rw [ons_logGIntBetaDeriv, abs_div, abs_of_pos hdenpos]
  have hC : 0 ≤ 2 * (|Real.cosh (2 * beta)| + 1) *
      (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by positivity
  exact div_le_div₀ hC hnum
    (sq_pos_of_pos (div_pos hgap0 two_pos)) hden

theorem ons_log_gInt_continuous_momenta_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => Real.log (ons_gInt b p.1 p.2)) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gInt b p.1 p.2) := by
    unfold ons_gInt
    fun_prop
  exact hg.log fun p =>
    (ons_gInt_pos_noncriticalNeighborhood (k1 := p.1) (k2 := p.2)
      hbeta hcrit hb).ne'

theorem ons_logGIntBetaDeriv_continuous_momenta_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => ons_logGIntBetaDeriv b p.1 p.2) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gInt b p.1 p.2) := by
    unfold ons_gInt
    fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => ons_gIntBetaDeriv b p.1 p.2) := by
    unfold ons_gIntBetaDeriv
    fun_prop
  exact hd.div hg fun p =>
    (ons_gInt_pos_noncriticalNeighborhood (k1 := p.1) (k2 := p.2)
      hbeta hcrit hb).ne'


theorem ons_hasDerivAt_innerIntegral_noncritical (beta k1 : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt
      (fun b => ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (ons_gInt b k1 k2))
      (∫ k2 in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv beta k1 k2) beta := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta / 2) ^ 2
  have hself : beta ∈ ons_noncriticalNeighborhood beta :=
    mem_of_mem_nhds (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b k2 => Real.log (ons_gInt b k1 k2))
    (F' := fun b k2 => ons_logGIntBetaDeriv b k1 k2)
    (bound := fun _ => C)
    (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
    exact ((ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hb).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hself).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((ons_logGIntBetaDeriv_continuous_momenta_noncritical hbeta hcrit hself).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with k2 _hk2 b hb
    simpa only [Real.norm_eq_abs, C] using
      (ons_logGIntBetaDeriv_abs_le_noncritical (k1 := k1) (k2 := k2)
        hbeta hcrit hb)
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k2 _hk2 b hb
    exact ons_hasDerivAt_log_gInt b k1 k2
      (ons_gInt_pos_noncriticalNeighborhood (k1 := k1) (k2 := k2)
        hbeta hcrit hb).ne'

theorem ons_noncriticalNeighborhood_ne_betaC {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    b ≠ ons_betaC := by
  intro heq
  subst b
  have hzero := hb.2.1
  change ons_noncriticalGap beta / 2 <
    |Real.sinh (2 * ons_betaC) - 1| at hzero
  rw [ons_betaC_sinh, sub_self, abs_zero] at hzero
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  linarith

theorem ons_innerLogIntegral_continuous_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b k1 k2)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hb)
    (-Real.pi) Real.pi

theorem ons_innerLogDerivIntegral_continuous_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b k1 k2) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_logGIntBetaDeriv_continuous_momenta_noncritical hbeta hcrit hb)
    (-Real.pi) Real.pi


theorem ons_hasDerivAt_doubleIntegral_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt
      (fun b => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt b k1 k2))
      (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta k1 k2) beta := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta / 2) ^ 2
  let B : ℝ := C * (2 * Real.pi)
  have hself : beta ∈ ons_noncriticalNeighborhood beta :=
    mem_of_mem_nhds (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b k1 k2))
    (F' := fun b k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b k1 k2)
    (bound := fun _ => B)
    (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
    exact (ons_innerLogIntegral_continuous_noncritical hbeta hcrit hb).aestronglyMeasurable
  · exact (ons_innerLogIntegral_continuous_noncritical hbeta hcrit hself).intervalIntegrable _ _
  · exact (ons_innerLogDerivIntegral_continuous_noncritical hbeta hcrit hself).aestronglyMeasurable
  · filter_upwards [] with k1 _hk1 b hb
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun k2 => ons_logGIntBetaDeriv b k1 k2) (C := C)
      (fun (k2 : ℝ) _hk2 => by
        simpa only [Real.norm_eq_abs, C] using
          (ons_logGIntBetaDeriv_abs_le_noncritical (k1 := k1) (k2 := k2)
            hbeta hcrit hb))
    calc
      ‖∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b k1 k2‖ ≤
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (show 0 < Real.pi - (-Real.pi) by
          linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k1 _hk1 b hb
    exact ons_hasDerivAt_innerIntegral_noncritical b k1 hb.1
      (ons_noncriticalNeighborhood_ne_betaC hbeta hcrit hb)


theorem ons_hasDerivAt_freeEnergyIntegral_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt ons_freeEnergyIntegral
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv beta k1 k2) beta := by
  unfold ons_freeEnergyIntegral
  exact (ons_hasDerivAt_doubleIntegral_noncritical beta hbeta hcrit).const_mul
    (1 / (8 * Real.pi ^ 2))

theorem ons_hasDerivAt_pressure_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt ons_pressure
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv beta k1 k2) beta := by
  change HasDerivAt (fun b => Real.log 2 + ons_freeEnergyIntegral b) _ beta
  simpa only [Pi.add_apply, zero_add] using (hasDerivAt_const beta (Real.log 2)).add
    (ons_hasDerivAt_freeEnergyIntegral_noncritical beta hbeta hcrit)


end StatMech.Onsager
