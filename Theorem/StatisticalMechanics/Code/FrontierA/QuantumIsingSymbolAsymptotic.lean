/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBogoliubovLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
open Filter
open scoped Topology


namespace StatMech.FrontierA

theorem cosh_sub_one_eq_two_sinh_half_sq (t : Real) :
    Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
  have hdouble := Real.cosh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hdouble
  nlinarith

theorem sinh_div_tendsto_one_right :
    Tendsto (fun t : Real => Real.sinh t / t) (𝓝[>] 0) (nhds 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  simpa [div_eq_inv_mul, smul_eq_mul] using h

theorem cosh_sub_one_div_sq_tendsto_half_right :
    Tendsto (fun t : Real => (Real.cosh t - 1) / t ^ 2)
      (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
  have hhalf : Tendsto (fun t : Real => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hfull : Tendsto (fun t : Real => t / 2) (nhds 0) (nhds 0) := by
        convert (tendsto_id : Tendsto (fun t : Real => t)
          (nhds 0) (nhds 0)).div_const 2 using 1 <;> norm_num
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      exact div_pos ht (by norm_num)
  have hs := sinh_div_tendsto_one_right.comp hhalf
  have hsSq := hs.pow 2
  have hscaled := (tendsto_const_nhds.mul hsSq : Tendsto
    (fun t : Real => (1 / 2 : Real) * (Real.sinh (t / 2) / (t / 2)) ^ 2)
    (𝓝[>] 0) (nhds ((1 / 2 : Real) * 1 ^ 2)))
  have heq : (fun t : Real => (Real.cosh t - 1) / t ^ 2) =ᶠ[𝓝[>] 0]
      (fun t : Real => (1 / 2 : Real) * (Real.sinh (t / 2) / (t / 2)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    rw [cosh_sub_one_eq_two_sinh_half_sq]
    field_simp [ht.ne']
  simpa using hscaled.congr' heq.symm

end StatMech.FrontierA
