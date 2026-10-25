/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFreeEnergyRapidityRadius_mem_Ioo
    {lam : Real} (hlam : 0 < lam) :
    sixVertexFreeEnergyRapidityRadius lam ∈ Set.Ioo 0 1 := by
  constructor
  · unfold sixVertexFreeEnergyRapidityRadius
    positivity
  · unfold sixVertexFreeEnergyRapidityRadius
    rw [Real.exp_lt_one_iff]
    linarith

theorem cosh_two_eq_sixVertexFreeEnergyRapidityRadius
    (lam : Real) :
    Real.cosh (2 * lam) =
      (sixVertexFreeEnergyRapidityRadius lam +
        (sixVertexFreeEnergyRapidityRadius lam)⁻¹) / 2 := by
  unfold sixVertexFreeEnergyRapidityRadius
  have hinv : (Real.exp (-2 * lam))⁻¹ = Real.exp (2 * lam) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [Real.cosh_eq, show -(2 * lam) = -2 * lam by ring, hinv,
    add_comm]

theorem sq_norm_one_sub_radius_exp_mul_I
    (r alpha : Real) :
    ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 =
      1 - 2 * r * Real.cos alpha + r ^ 2 := by
  rw [show Complex.I * (alpha : Complex) =
      (alpha : Complex) * Complex.I by ring]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq alpha]


theorem log_radius_add_inv_div_two_sub_cos
    {r : Real} (hr : r ∈ Set.Ioo 0 1) (alpha : Real) :
    Real.log ((r + r⁻¹) / 2 - Real.cos alpha) =
      2 * Real.log ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ -
        Real.log (2 * r) := by
  have hr0 : 0 < r := hr.1
  have honeSub : 1 - r ≠ 0 := by linarith [hr.2]
  have hsquare : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero honeSub
  have hdelta : 1 < (r + r⁻¹) / 2 := by
    rw [one_lt_div (by norm_num : (0 : Real) < 2)]
    have hrepr : r + r⁻¹ - 2 = (1 - r) ^ 2 / r := by
      field_simp [hr0.ne']
      ring
    have : 0 < r + r⁻¹ - 2 := by
      rw [hrepr]
      exact div_pos hsquare hr0
    linarith
  have harg :
      (r + r⁻¹) / 2 - Real.cos alpha =
        ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 /
            (2 * r) := by
    rw [sq_norm_one_sub_radius_exp_mul_I]
    field_simp [hr0.ne']
    ring
  have hleft : 0 < (r + r⁻¹) / 2 - Real.cos alpha := by
    linarith [Real.cos_le_one alpha]
  have hnorm :
      ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ ≠ 0 := by
    intro hzero
    have hsqzero :
        ‖(1 : Complex) -
          (r : Complex) * Complex.exp (Complex.I * alpha)‖ ^ 2 = 0 := by
      rw [hzero]
      norm_num
    rw [hsqzero, zero_div] at harg
    linarith
  rw [harg, Real.log_div (pow_ne_zero 2 hnorm)
    (mul_ne_zero (by norm_num) hr0.ne'), Real.log_pow]
  norm_num


end
end StatMech.FrontierD
