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
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part4
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingTrotterModeContribution_succ
    (beta h : Real) (n : Nat) (k : Real) :
    quantumIsingTrotterModeContribution beta h (n + 1) k =
      quantumIsingShiftedTrotterModeContribution beta h n k := by
  simp only [quantumIsingTrotterModeContribution, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, quantumIsingShiftedTrotterModeContribution,
    quantumIsingModeScalarNormalization, quantumIsingScaledArcosh]
  norm_num only [Nat.cast_add, Nat.cast_one]

theorem quantumIsingTrotterModeContribution_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (quantumIsingTrotterModeContribution beta h)
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
  have hshift := quantumIsingShiftedTrotterModeContribution_tendstoUniformly
    beta h hbeta hh
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    ((Metric.tendstoUniformly_iff.mp hshift) epsilon hepsilon))
  rw [eventually_atTop]
  refine ⟨N + 1, fun L hL k ↦ ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.zero_lt_succ N) hL
  have hpred : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
  have hpredN : N ≤ L - 1 := by omega
  rw [← hpred, quantumIsingTrotterModeContribution_succ]
  exact hN (L - 1) hpredN k

theorem continuous_quantumIsingTrotterModeLimit (beta h : Real) :
    Continuous (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) :=
  continuous_const.add (continuous_const.mul
    (continuous_quantumIsingModeLog beta h))

theorem periodic_quantumIsingTrotterModeLimit (beta h : Real) :
    Function.Periodic
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
      (2 * Real.pi) := by
  intro k
  dsimp only
  rw [periodic_quantumIsingModeLog beta h k]

theorem quantumIsingTrotterModeContribution_midpoint_average_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun L : Nat ↦
      (1 / (L : Real)) * ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi))
      atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
  have hmid := ons_riemann_periodic_midpoint_average_of_tendstoUniformly
    (quantumIsingTrotterModeContribution beta h)
    (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)
    (continuous_quantumIsingTrotterModeLimit beta h)
    (periodic_quantumIsingTrotterModeLimit beta h)
    (quantumIsingTrotterModeContribution_tendstoUniformly beta h hbeta hh)
  exact hmid

theorem quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh
    {A : Real} (hA : 1 ≤ A) (L : Nat) :
    (quantumIsingSpectralRoot A)⁻¹ ^ L =
      Real.exp (-(L : Real) * Real.arcosh A) := by
  have hroot : quantumIsingSpectralRoot A =
      Real.exp (Real.arcosh A) := by
    rw [Real.exp_arcosh hA]
    rfl
  rw [hroot, ← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring

theorem quantumIsingTrotterModeContribution_eq_spectralRoot
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) (k : Real) :
    quantumIsingTrotterModeContribution beta h L k =
      (L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
        (L : Real) * Real.arcosh
          (quantumIsingTrotterReducedParameter beta h L k) +
        2 * Real.log
          (1 + (quantumIsingSpectralRoot
            (quantumIsingTrotterReducedParameter beta h L k))⁻¹ ^ L) := by
  have hL : 0 < L := by have := (Fact.out : 2 < L); omega
  have hA : 1 ≤ quantumIsingTrotterReducedParameter beta h L k :=
    quantumIsingTrotterReducedParameter_one_le beta h L k
      hbeta.le hh.le hL hx1
  rw [quantumIsingTrotterModeContribution, if_neg hL.ne',
    quantumIsingRapidityCorrection]
  rw [quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh hA]
  ring

theorem two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (hbeta : 0 < beta) (hh : 0 < h)
    (hx1 : beta * h / (2 * L) < 1) :
    (2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L 1 1‖) / L =
      (1 / (L : Real)) * ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi) := by
  rw [two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven
    beta h L hbeta hh hx1]
  have hsum :
      (∑ k ∈ Finset.range L,
        ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
          (L : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h L
              (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi)) +
          2 * Real.log
            (1 + (quantumIsingSpectralRoot
              (quantumIsingTrotterReducedParameter beta h L
                (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L))) =
      ∑ k ∈ Finset.range L,
        quantumIsingTrotterModeContribution beta h L
          (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (quantumIsingTrotterModeContribution_eq_spectralRoot
      beta h L hbeta hh hx1 _).symm
  rw [hsum]
  ring

end StatMech.FrontierA
