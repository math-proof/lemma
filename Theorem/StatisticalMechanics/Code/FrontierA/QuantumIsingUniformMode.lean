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
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingRapidityCorrection_eq_cosh (x : Real) :
    quantumIsingRapidityCorrection x =
      2 * Real.log 2 + 2 * Real.log (Real.cosh (x / 2)) := by
  have hprodOne :
      Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hprodNeg :
      Real.exp (-x / 2) * Real.exp (-(x / 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor :
      1 + Real.exp (-x) =
        2 * Real.exp (-x / 2) * Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    symm
    calc
      2 * Real.exp (-x / 2) *
          ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) =
          Real.exp (-x / 2) * Real.exp (x / 2) +
            Real.exp (-x / 2) * Real.exp (-(x / 2)) := by ring
      _ = 1 + Real.exp (-x) := by rw [hprodOne, hprodNeg]
  have hlog : Real.log (1 + Real.exp (-x)) =
      Real.log 2 + Real.log (Real.exp (-x / 2)) +
        Real.log (Real.cosh (x / 2)) := by
    rw [hfactor,
      Real.log_mul
        (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))
        (Real.cosh_pos _).ne',
      Real.log_mul (by norm_num) (Real.exp_ne_zero _)]
  unfold quantumIsingRapidityCorrection
  rw [hlog, Real.log_exp]
  ring

theorem quantumIsingRapidityCorrection_hasDerivAt (x : Real) :
    HasDerivAt quantumIsingRapidityCorrection (Real.tanh (x / 2)) x := by
  have heq : quantumIsingRapidityCorrection =
      fun y ↦ 2 * Real.log 2 + 2 * Real.log (Real.cosh (y / 2)) :=
    funext quantumIsingRapidityCorrection_eq_cosh
  rw [heq]
  convert (Real.hasDerivAt_log (Real.cosh_pos (x / 2)).ne').comp x
      ((Real.hasDerivAt_cosh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)) |>.const_mul 2 |>.const_add
        (2 * Real.log 2) using 1 <;>
    rw [Real.tanh_eq_sinh_div_cosh] <;> ring

theorem quantumIsingRapidityCorrection_lipschitz :
    LipschitzWith 1 quantumIsingRapidityCorrection := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (quantumIsingRapidityCorrection_hasDerivAt x).differentiableAt
  · intro x
    rw [(quantumIsingRapidityCorrection_hasDerivAt x).deriv]
    simpa only [Real.nnnorm_of_nonneg (abs_nonneg _), NNReal.coe_one,
      Real.norm_eq_abs] using (Real.abs_tanh_lt_one (x / 2)).le

end StatMech.FrontierA
