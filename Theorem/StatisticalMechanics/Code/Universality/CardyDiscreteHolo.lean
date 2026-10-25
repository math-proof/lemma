/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo


namespace StatMech.Universality

open Complex


theorem cardyOmega_cube : cardyOmega ^ 3 = 1 := by
  unfold cardyOmega
  rw [← Complex.exp_nat_mul,
      show (3 : ℕ) * ((2 * Real.pi / 3 : ℝ) * Complex.I)
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact_mod_cast Complex.exp_two_pi_mul_I


theorem cardyOmega_ne_one : cardyOmega ≠ 1 := by
  unfold cardyOmega
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.exp_ofReal_mul_I_re] at hre
  simp only [Complex.one_re] at hre
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hc] at hre; norm_num at hre


theorem cardyOmega_sum_zero : 1 + cardyOmega + cardyOmega ^ 2 = 0 := by
  have h3 : cardyOmega ^ 3 - 1 = 0 := by rw [cardyOmega_cube]; ring
  have hfac : cardyOmega ^ 3 - 1 = (cardyOmega - 1) * (1 + cardyOmega + cardyOmega ^ 2) := by
    ring
  rw [hfac] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) cardyOmega_ne_one
  · exact h


end StatMech.Universality
