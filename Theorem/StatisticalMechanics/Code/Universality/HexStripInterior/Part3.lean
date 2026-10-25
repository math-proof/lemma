/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexStripInterior.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStrip_halfStep_re (h : ℤ) :
    (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]; norm_num


theorem hexStrip_halfStep_im (h : ℤ) :
    (HexWalk.halfStep h).im = (1 / 2) * Real.sin (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]; norm_num


theorem hexStrip_normSq_halfStep (h : ℤ) : Complex.normSq (HexWalk.halfStep h) = 1 / 4 := by
  rw [Complex.normSq_apply, hexStrip_halfStep_re, hexStrip_halfStep_im]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 6 + (h : ℝ) * (Real.pi / 3))]


theorem hexStrip_normSq_two_one (h0 : ℤ) :
    Complex.normSq (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) = 7 / 4 := by
  have hre : (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))).re
      = 2 * (HexWalk.halfStep h0).re + (HexWalk.halfStep (h0 + (-1))).re := by
    simp [Complex.add_re, Complex.mul_re]
  have him : (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))).im
      = 2 * (HexWalk.halfStep h0).im + (HexWalk.halfStep (h0 + (-1))).im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [Complex.normSq_apply, hre, him,
    hexStrip_halfStep_re, hexStrip_halfStep_im, hexStrip_halfStep_re, hexStrip_halfStep_im]
  have hB : (Real.pi / 6 + ((h0 + (-1) : ℤ) : ℝ) * (Real.pi / 3))
      = (Real.pi / 6 + (h0 : ℝ) * (Real.pi / 3)) - Real.pi / 3 := by push_cast; ring
  rw [hB]
  set A := Real.pi / 6 + (h0 : ℝ) * (Real.pi / 3) with hA
  rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sin_sq_add_cos_sq A, hsqrt]


theorem hexStrip_two_one_add_ne_zero (h0 h : ℤ) :
    2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) + HexWalk.halfStep h ≠ 0 := by
  intro hc
  have heq : 2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) = - HexWalk.halfStep h := by
    linear_combination hc
  have h1 := hexStrip_normSq_two_one h0
  rw [heq, Complex.normSq_neg, hexStrip_normSq_halfStep] at h1
  norm_num at h1


theorem hexStrip_outer_ne (a : ℂ) (h0 h : ℤ) :
    a + HexWalk.halfStep (h0 + 3)
      ≠ (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h := by
  intro hc
  rw [hexW1Exit_halfStep_add_three] at hc
  exact hexStrip_two_one_add_ne_zero h0 h (by linear_combination -hc)


end StatMech.Universality
