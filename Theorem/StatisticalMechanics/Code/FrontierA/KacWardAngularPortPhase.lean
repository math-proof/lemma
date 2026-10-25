/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3


namespace StatMech.FrontierA

open SimpleGraph

theorem kwAngularUnit_chord_of_lt {a b : ℝ} (hab : a < b) :
    kwAngularUnit b - kwAngularUnit a =
      ((2 * Real.sin ((b - a) / 2) : ℝ) : ℂ) *
        kwAngularUnit ((a + b) / 2 + Real.pi / 2) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, kwAngularUnit_re]
    rw [Real.cos_sub_cos, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, kwAngularUnit_im]
    rw [Real.sin_sub_sin, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring

theorem kwAngularUnit_chord_of_gt {a b : ℝ} (hba : b < a) :
    kwAngularUnit b - kwAngularUnit a =
      ((2 * Real.sin ((a - b) / 2) : ℝ) : ℂ) *
        kwAngularUnit ((a + b) / 2 - Real.pi / 2) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, kwAngularUnit_re]
    rw [Real.cos_sub_cos, Real.cos_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.sin_neg]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, kwAngularUnit_im]
    rw [Real.sin_sub_sin, Real.sin_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.sin_neg]
    ring


end StatMech.FrontierA
