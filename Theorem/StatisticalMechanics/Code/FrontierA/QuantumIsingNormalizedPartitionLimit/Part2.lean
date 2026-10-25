/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductComparison
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionSandwich
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionLimit.Part2
open Filter
open scoped Topology


namespace StatMech.FrontierA

theorem quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity
    (beta h : Real) (n : Nat) (hbeta : 0 < beta) (hh : 0 < h) :
    quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n =
      -quantumIsingNormalizedDiagonalLogDensity beta h n / beta := by
  let L := n + 3
  have hL : L ≠ 0 := by dsimp only [L]; omega
  have hpos : 0 < beta * h / (2 * (L : Real)) := by positivity
  unfold quantumIsingCofinalPeriodicTrotterFreeEnergy
  rw [quantumIsingPeriodicTrotterAction_eq_log_pathPartition beta h L L hL,
    ← quantumIsingNormalizedDiagonalPartition_eq_pathPartition beta h L hpos]
  unfold quantumIsingNormalizedDiagonalLogDensity
  dsimp only [L]
  ring

theorem quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingCofinalPeriodicTrotterFreeEnergy beta h) atTop
      (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
  have htend := (quantumIsingNormalizedDiagonalLogDensity_tendsto
    beta h hbeta hh).neg.div_const beta
  apply htend.congr'
  filter_upwards with n
  exact (quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity
    beta h n hbeta hh).symm

theorem quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop
      (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
  have hfinite := quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto
    beta h hbeta hh
  have herr : Tendsto (fun n : Nat ↦ 1 / (2 * (n + 3 : Real)))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : Real)).comp
      (tendsto_add_atTop_nat 3)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
    field_simp
  have hdiffAbs : Tendsto (fun n : Nat ↦
      |quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3) -
        quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n|)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ ?_) herr
    unfold quantumIsingCofinalPeriodicTrotterFreeEnergy
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (quantumIsingPeriodicTrotterFreeEnergy_uniform_bound
        beta h (n + 3) (by omega) hbeta (mul_pos hbeta hh) (L := n + 3)
          (by omega))
  have hdiff : Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3) -
        quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using hdiffAbs
  convert hfinite.add hdiff using 1
  · funext n
    ring
  · ring

theorem quantumIsing_half_modeIntegral_eq_logPressure (beta h : Real) :
    (1 / 2 : Real) * ((1 / (2 * Real.pi)) *
      ∫ k in (-Real.pi)..Real.pi,
        (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)) =
      Real.log 2 + (1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
  have hmode : IntervalIntegrable (quantumIsingModeLog beta h)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (continuous_quantumIsingModeLog beta h).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const
    (hmode.const_mul 2), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  norm_num only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring


theorem quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  have h := quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw
    beta h hbeta hh
  convert h using 1
  unfold quantumIsingFreeEnergyValue
  rw [quantumIsing_half_modeIntegral_eq_logPressure]
  ring

end StatMech.FrontierA
