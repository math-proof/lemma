/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicVarying
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicSectorLimit
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingZeroOneSectorLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingZeroOneSectorLogDensity beta h) atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hleft := StatMech.Onsager.ons_riemann_periodic_shifted_average_of_tendstoUniformly
    (quantumIsingTrotterModeContribution beta h)
    (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
    (continuous_quantumIsingTrotterModeLimit beta h)
    (periodic_quantumIsingTrotterModeLimit beta h)
    (quantumIsingTrotterModeContribution_tendstoUniformly beta h hbeta hh)
  have hxlim : Tendsto (fun L : Nat ↦ beta * h / (2 * (L : Real)))
      atTop (nhds 0) := by
    have hzero := tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)
    convert hzero using 1
    funext L
    ring
  have hxlt : ∀ᶠ L : Nat in atTop,
      beta * h / (2 * (L : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  have hleftShift := hleft.comp (tendsto_add_atTop_nat 3)
  apply hleftShift.congr'
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hxlt] with n hx1
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  dsimp only [Function.comp_apply]
  change (1 / ((n + 3 : Nat) : Real)) *
      ∑ k ∈ Finset.range (n + 3),
        quantumIsingTrotterModeContribution beta h (n + 3)
          (2 * Real.pi * k / ((n + 3 : Nat) : Real) - Real.pi) =
    quantumIsingZeroOneSectorLogDensity beta h n
  unfold quantumIsingZeroOneSectorLogDensity
  simpa only [Fin.val_zero, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
    zero_div, add_zero] using
    (two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage
      beta h (n + 3) 0 hbeta hh hx1).symm

end StatMech.FrontierA
