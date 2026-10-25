/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo


namespace StatMech.Universality

open Complex


theorem isingLambda_ne : isingLambda ≠ 0 := by
  unfold isingLambda; exact Complex.exp_ne_zero _


theorem isingLambda_sq : isingLambda ^ 2 = Complex.I := by
  unfold isingLambda
  rw [← Complex.exp_nat_mul,
      show (2 : ℕ) * ((Real.pi / 4 : ℝ) * Complex.I)
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp


theorem isingSqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (((Real.sqrt 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Real.sq_sqrt (by norm_num)]
  norm_num


theorem isingSqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'


theorem isingLambda_magic : isingLambda - isingLambda⁻¹ = Complex.I * (Real.sqrt 2 : ℂ) := by
  unfold isingLambda
  rw [← Complex.exp_neg,
      show -((Real.pi / 4 : ℝ) * Complex.I) = (-((Real.pi / 4 : ℝ) : ℂ)) * Complex.I by
        push_cast; ring]
  have hsin : Complex.sin ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_four]
  have h := Complex.two_sin (((Real.pi / 4 : ℝ) : ℂ))
  have key : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
      - Complex.exp ((-((Real.pi / 4 : ℝ) : ℂ)) * Complex.I)
      = 2 * Complex.sin ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    rw [h]; ring_nf; rw [hI]; ring
  rw [key, hsin]; push_cast; ring


theorem sqrt2_mul_isingLambda : (Real.sqrt 2 : ℂ) * isingLambda = 1 + Complex.I := by
  unfold isingLambda
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := isingSqrt2_sq
  push_cast
  linear_combination (1 / 2 : ℂ) * hs + ((1 / 2 : ℂ) * Complex.I) * hs


theorem isingLambda_val : isingLambda = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [eq_div_iff isingSqrt2_ne, mul_comm]; exact sqrt2_mul_isingLambda


theorem isingLambda_inv : isingLambda⁻¹ = (Real.sqrt 2 : ℂ) - isingLambda := by
  have h : isingLambda * ((Real.sqrt 2 : ℂ) - isingLambda) = 1 := by
    rw [mul_sub, mul_comm isingLambda (Real.sqrt 2 : ℂ), sqrt2_mul_isingLambda, ← sq,
        isingLambda_sq]
    ring
  symm
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)


end StatMech.Universality
