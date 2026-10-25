/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem exp_neg_two_arctan_mul_I (r : ℝ) :
    Complex.exp (((-2 * Real.arctan r : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) - (r : ℂ) * Complex.I) /
        ((1 : ℂ) + (r : ℂ) * Complex.I) := by
  have hsqrt : Real.sqrt (1 + r ^ 2) ≠ 0 := by positivity
  have hsquare : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hcos : Real.cos (-2 * Real.arctan r) =
      (1 - r ^ 2) / (1 + r ^ 2) := by
    rw [show -2 * Real.arctan r = -(2 * Real.arctan r) by ring]
    rw [Real.cos_neg, Real.cos_two_mul, Real.cos_arctan]
    field_simp
    rw [hsquare]
    ring
  have hsin : Real.sin (-2 * Real.arctan r) =
      (-2 * r) / (1 + r ^ 2) := by
    rw [show -2 * Real.arctan r = -(2 * Real.arctan r) by ring]
    rw [Real.sin_neg, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    field_simp
    rw [hsquare]
  rw [Complex.exp_ofReal_mul_I, hcos, hsin]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.one_re, Complex.ofReal_re, Complex.I_re, Complex.add_im,
      Complex.sub_im, Complex.mul_im, Complex.div_im, Complex.one_im,
      Complex.ofReal_im, Complex.I_im, Complex.normSq_apply, mul_zero,
      mul_one, zero_add, add_zero, sub_zero, zero_sub]
  all_goals
    field_simp
    ring


end
end StatMech.FrontierD
