/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer.Part2
import Def.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part2
open scoped Real
open MeasureTheory Interval


namespace StatMech.Onsager

theorem ons_inner_integral_norm_le (beta k1 : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
    (hshi : Real.sinh (2 * beta) ≤ 2) :
    ‖∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)‖ ≤
      ons_criticalInnerBound := by
  unfold ons_criticalInnerBound
  apply intervalIntegral.norm_integral_le_abs_of_norm_le
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    rw [Real.norm_eq_abs]
    have hk2' := Set.uIoc_subset_uIcc hk2
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2'
    exact ons_log_gInt_bound beta k1 k2 hslo hshi hk2' hk20
  · exact ons_intervalIntegrable_criticalLogBound

theorem ons_double_integral_tendsto_betaC :
    Filter.Tendsto
      (fun beta : ℝ => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2))
      (nhds ons_betaC)
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt ons_betaC k1 k2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _k1 : ℝ => ons_criticalInnerBound)
  · filter_upwards [ons_eventually_sinh_bounds] with beta hbeta
    exact (ons_inner_integral_continuous_near_betaC
      beta hbeta.1 hbeta.2).aestronglyMeasurable
  · filter_upwards [ons_eventually_sinh_bounds] with beta hbeta
    filter_upwards [] with k1 hk1
    exact ons_inner_integral_norm_le beta k1 hbeta.1 hbeta.2
  · exact intervalIntegrable_const
  · filter_upwards [] with k1 hk1
    exact ons_inner_integral_tendsto_betaC k1

theorem ons_continuousAt_freeEnergyIntegral_betaC :
    ContinuousAt ons_freeEnergyIntegral ons_betaC := by
  unfold ons_freeEnergyIntegral
  exact (ons_double_integral_tendsto_betaC.const_mul
    (1 / (8 * Real.pi ^ 2)))


theorem ons_continuousAt_pressure_betaC :
    ContinuousAt ons_pressure ons_betaC := by
  unfold ons_pressure
  exact continuousAt_const.add ons_continuousAt_freeEnergyIntegral_betaC

end StatMech.Onsager
