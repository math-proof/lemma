/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexVertex.Part2


namespace StatMech.Universality

open Complex


theorem hexCos_pi8_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos, Real.pi_le_four]


theorem hexChi_pos : 0 < hexChi := by
  unfold hexChi
  have := hexCos_pi8_pos
  positivity


theorem hexChi_eq_sqrt : hexChi = 1 / Real.sqrt (2 + Real.sqrt 2) := by
  unfold hexChi
  congr 1
  
  have hcospos := hexCos_pi8_pos
  have hpos : (0 : ℝ) ≤ 2 * Real.cos (Real.pi / 8) := by
    positivity
  rw [show (2 + Real.sqrt 2 : ℝ) = (2 * Real.cos (Real.pi / 8)) ^ 2 by
        have hcos2 : Real.cos (Real.pi / 8) ^ 2 = (1 + Real.cos (Real.pi / 4)) / 2 := by
          have := Real.cos_sq (Real.pi / 8)
          rw [this]; ring_nf
        have hcosq : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        rw [mul_pow, hcos2, hcosq]; ring]
  rw [Real.sqrt_sq hpos]


theorem hexPair_zero :
    hexOmega * hexLambda ^ (-4 : ℤ) + hexOmega ^ 2 * hexLambda ^ (4 : ℤ) = 0 := by
  rw [hexOmega_sq]
  unfold hexOmega hexLambda
  rw [hexExpI_zpow, hexExpI_zpow, hexExpI_mul, hexExpI_mul]
  
  have h1 : (2 * Real.pi / 3) + (((-4 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
      = 3 * Real.pi / 2 := by push_cast; ring
  
  
  have h2 : (2 * (2 * Real.pi / 3)) + (((4 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
      = -(3 * Real.pi / 2) + 2 * Real.pi := by push_cast; ring
  rw [h1, h2]
  
  rw [show (((-(3 * Real.pi / 2) + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = ((-(3 * Real.pi / 2) : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [hexExpI_add_neg]
  
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add]
    simp
  rw [hcos]; simp


theorem hexTriplet_zero :
    (1 : ℂ) + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
      + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ)) = 0 := by
  
  have hsum : hexOmega * hexLambda ^ (-1 : ℤ) + hexOmega ^ 2 * hexLambda ^ (1 : ℤ)
      = 2 * (Real.cos (7 * Real.pi / 8) : ℂ) := by
    rw [hexOmega_sq]
    unfold hexOmega hexLambda
    rw [hexExpI_zpow, hexExpI_zpow, hexExpI_mul, hexExpI_mul]
    have h1 : (2 * Real.pi / 3) + (((-1 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
        = 7 * Real.pi / 8 := by push_cast; ring
    have h2 : (2 * (2 * Real.pi / 3)) + (((1 : ℤ) : ℝ) * (-(5 * Real.pi / 24)))
        = -(7 * Real.pi / 8) + 2 * Real.pi := by push_cast; ring
    rw [h1, h2]
    rw [show (((-(7 * Real.pi / 8) + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
          = ((-(7 * Real.pi / 8) : ℝ) : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by
          push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexExpI_add_neg]
  
  rw [show (1 : ℂ) + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
          + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ))
        = 1 + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ)
              + hexOmega ^ 2 * hexLambda ^ (1 : ℤ)) by ring,
      hsum]
  have hcos7 : Real.cos (7 * Real.pi / 8) = - Real.cos (Real.pi / 8) := by
    rw [show (7 * Real.pi / 8 : ℝ) = Real.pi - Real.pi / 8 by ring, Real.cos_pi_sub]
  unfold hexChi
  have hcos_ne : (Real.cos (Real.pi / 8) : ℂ) ≠ 0 := by
    exact_mod_cast hexCos_pi8_pos.ne'
  rw [hcos7,
      show ((-Real.cos (Real.pi / 8) : ℝ) : ℂ) = -(Real.cos (Real.pi / 8) : ℂ) by push_cast; ring,
      show ((1 / (2 * Real.cos (Real.pi / 8)) : ℝ) : ℂ)
        = 1 / (2 * (Real.cos (Real.pi / 8) : ℂ)) by push_cast; ring]
  field_simp
  ring


end StatMech.Universality
