/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
import Mathlib.Analysis.Calculus.MeanValue
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingElevenSectorLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingElevenSectorLogDensity beta h) atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hmid := quantumIsingTrotterModeContribution_midpoint_average_tendsto
    beta h hbeta hh
  have hxlim : Tendsto (fun L : Nat ↦ beta * h / (2 * (L : Real)))
      atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)
    convert h using 1
    funext L
    ring
  have hxlt : ∀ᶠ L : Nat in atTop, beta * h / (2 * (L : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  have hmidShift := hmid.comp (tendsto_add_atTop_nat 3)
  apply hmidShift.congr'
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hxlt] with n hx1
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  dsimp only [Function.comp_apply]
  change (1 / ((n + 3 : Nat) : Real)) *
      ∑ k ∈ Finset.range (n + 3),
        quantumIsingTrotterModeContribution beta h (n + 3)
          (2 * Real.pi * (k + (1 : Real) / 2) /
            ((n + 3 : Nat) : Real) - Real.pi) =
    quantumIsingElevenSectorLogDensity beta h n
  unfold quantumIsingElevenSectorLogDensity
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage
      beta h (n + 3) hbeta hh hx1).symm

end StatMech.FrontierA
