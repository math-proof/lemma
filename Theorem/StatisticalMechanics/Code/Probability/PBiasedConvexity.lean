/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedIntegralHC.Part2
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem pcx_gpp_bracket_nonneg {p q a c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ha : 0 < a) (hc : 0 < c)
    (hcon : (1 - p) * a + p * c = 1) :
    4 * p * (1 - p) ≤ p * a ^ (q - 2) + (1 - p) * c ^ (q - 2) := by
  
  have hac_bound : 4 * p * (1 - p) * (a * c) ≤ 1 := by
    nlinarith [sq_nonneg ((1 - p) * a - p * c)]
  have hac_pos : 0 < a * c := mul_pos ha hc
  
  have hstep2 : 4 * p * (1 - p) ≤ (a * c) ^ (q - 2) := by
    rcases le_total (a * c) 1 with hw1 | hw1
    · 
      have hge1 : (1 : ℝ) ≤ (a * c) ^ (q - 2) := by
        rw [show (1 : ℝ) = (a * c) ^ (0 : ℝ) by rw [Real.rpow_zero]]
        exact Real.rpow_le_rpow_of_exponent_ge hac_pos hw1 (by linarith)
      have h4le1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
      linarith
    · 
      have hge : (a * c) ^ (-1 : ℝ) ≤ (a * c) ^ (q - 2) :=
        Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
      rw [Real.rpow_neg hac_pos.le, Real.rpow_one] at hge
      have hwinv : 4 * p * (1 - p) ≤ (a * c)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hac_pos]; linarith
      linarith
  
  have hmul : a ^ (q - 2) * c ^ (q - 2) = (a * c) ^ (q - 2) := (Real.mul_rpow ha.le hc.le).symm
  set X := p * a ^ (q - 2) with hX
  set Y := (1 - p) * c ^ (q - 2) with hY
  have hXY : X * Y = p * (1 - p) * (a * c) ^ (q - 2) := by rw [hX, hY, ← hmul]; ring
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hYnn : 0 ≤ Y := by rw [hY]; positivity
  have hamgm : 2 * Real.sqrt (X * Y) ≤ X + Y := by
    nlinarith [sq_nonneg (Real.sqrt X - Real.sqrt Y), Real.sq_sqrt hXnn, Real.sq_sqrt hYnn,
      Real.mul_self_sqrt (mul_nonneg hXnn hYnn), Real.sqrt_mul hXnn Y]
  have hppnn : 0 ≤ p * (1 - p) := by nlinarith
  have hXYlb : (2 * p * (1 - p)) ^ 2 ≤ X * Y := by rw [hXY]; nlinarith [hstep2, hppnn]
  have hsqrtlb : 2 * p * (1 - p) ≤ Real.sqrt (X * Y) := by
    rw [show 2 * p * (1 - p) = Real.sqrt ((2 * p * (1 - p)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hXYlb
  linarith [hamgm, hsqrtlb]


end StatMech.Probability
