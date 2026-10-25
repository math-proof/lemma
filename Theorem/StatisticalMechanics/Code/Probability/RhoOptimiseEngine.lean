/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators
open Finset
open Real Filter Topology
open intervalIntegral MeasureTheory

set_option linter.style.longLine false


namespace StatMech.Probability

theorem roe_integral_exp_mul (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hc, integral_exp]
  rw [smul_eq_mul]; field_simp


theorem roe_integral_exp_le (t : ℝ) (ht : 0 < t) :
    (∫ u in (0:ℝ)..1, Real.exp (-(t / 2) * u)) ≤ 2 / t := by
  have hc : -(t / 2) ≠ 0 := by intro h; nlinarith
  rw [roe_integral_exp_mul (-(t / 2)) hc 0 1]
  rw [mul_one, mul_zero, Real.exp_zero]
  have hexp : (0:ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
  have key : (Real.exp (-(t / 2)) - 1) / -(t / 2) = (1 - Real.exp (-(t / 2))) / (t / 2) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hexp]


theorem roe_integral_one_sub_pow (n : ℕ) :
    ∫ u in (0:ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) (fun x => x ^ n) 1
  rw [h]
  norm_num [integral_pow]


theorem roe_rpow_integrable (δ : ℝ) (hδ0 : 0 < δ) :
    IntervalIntegrable (fun u => δ ^ (u / (2 - u))) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num)]
  apply ContinuousOn.congr (f := fun u => Real.exp (Real.log δ * (u / (2 - u))))
  · apply ContinuousOn.comp (g := Real.exp) Real.continuous_exp.continuousOn
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_id (by fun_prop)
      intro x hx
      simp only [Set.mem_Icc] at hx
      intro h; linarith [hx.2]
    · exact Set.mapsTo_univ _ _
  · intro u _; simp only; rw [Real.rpow_def_of_pos hδ0]


theorem roe_integral_rhs_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u))) ≤ 2 / (-(Real.log δ)) := by
  have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
  refine le_trans ?_ (roe_integral_exp_le _ ht)
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact roe_rpow_integrable δ hδ0
  · apply Continuous.intervalIntegrable; fun_prop
  · intro u hu
    simp only [Set.mem_Icc] at hu
    rw [Real.rpow_def_of_pos hδ0]
    apply Real.exp_le_exp.mpr
    have hlogneg : Real.log δ < 0 := Real.log_neg hδ0 hδ1
    have h2u : (0:ℝ) < 2 - u := by linarith [hu.2]
    rw [show -(-(Real.log δ) / 2) * u = Real.log δ * (u / 2) from by ring]
    apply mul_le_mul_of_nonpos_left _ (le_of_lt hlogneg)
    rw [div_le_div_iff₀ (by norm_num) h2u]
    nlinarith [hu.1]


end StatMech.Probability
