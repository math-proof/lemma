/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2


namespace StatMech.FrontierA

theorem kw_halfAngle_two_eq_neg_four_of_odd_full_turn
    (x₁ x₂ y₁ y₂ y₃ y₄ : ℝ)
    (hturn : x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = 2 * Real.pi ∨
      x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = -(2 * Real.pi)) :
    Complex.exp (((x₁ : ℂ) * Complex.I) / 2) *
        Complex.exp (((x₂ : ℂ) * Complex.I) / 2) =
      -(Complex.exp (((y₁ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₂ : ℂ) * Complex.I) / 2) *
        (Complex.exp (((y₃ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₄ : ℂ) * Complex.I) / 2))) := by
  let X : ℂ := ((x₁ : ℂ) * Complex.I) / 2 +
    ((x₂ : ℂ) * Complex.I) / 2
  let Y : ℂ := ((y₁ : ℂ) * Complex.I) / 2 +
    ((y₂ : ℂ) * Complex.I) / 2 +
    ((y₃ : ℂ) * Complex.I) / 2 +
    ((y₄ : ℂ) * Complex.I) / 2
  have hleft : Complex.exp (((x₁ : ℂ) * Complex.I) / 2) *
      Complex.exp (((x₂ : ℂ) * Complex.I) / 2) = Complex.exp X := by
    rw [← Complex.exp_add]
  have hright : Complex.exp (((y₁ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₂ : ℂ) * Complex.I) / 2) *
        (Complex.exp (((y₃ : ℂ) * Complex.I) / 2) *
          Complex.exp (((y₄ : ℂ) * Complex.I) / 2)) = Complex.exp Y := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hleft, hright]
  rcases hturn with hturn | hturn
  · have hXY : X = Y + (Real.pi : ℂ) * Complex.I := by
      dsimp only [X, Y]
      have hturn' : (x₁ : ℂ) + x₂ - (y₁ + y₂ + y₃ + y₄) =
          (2 * Real.pi : ℝ) := by exact_mod_cast hturn
      push_cast at hturn'
      linear_combination (Complex.I / 2) * hturn'
    rw [hXY, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · have hXY : X = Y - (Real.pi : ℂ) * Complex.I := by
      dsimp only [X, Y]
      have hturn' : (x₁ : ℂ) + x₂ - (y₁ + y₂ + y₃ + y₄) =
          (-(2 * Real.pi) : ℝ) := by exact_mod_cast hturn
      push_cast at hturn'
      linear_combination (Complex.I / 2) * hturn'
    have hnegPi : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [hXY, sub_eq_add_neg, Complex.exp_add, hnegPi]
    ring


end StatMech.FrontierA
