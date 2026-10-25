/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
open scoped ComplexConjugate


namespace StatMech.FrontierA

theorem asano_quadratic_contraction
    (A E D z : ℂ)
    (hstable : ∀ t : ℂ, ‖t‖ < 1 → A + E * t + D * t ^ 2 ≠ 0)
    (hz : ‖z‖ < 1) : A + D * z ≠ 0 := by
  intro hzero
  by_cases hD : D = 0
  · subst D
    have hA : A = 0 := by simpa using hzero
    exact hstable 0 (by simp) (by simp [hA])
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (E ^ 2 - 4 * D * A) (by omega : 0 < 2)
    let x : ℂ := (-E + r) / (2 * D)
    let y : ℂ := (-E - r) / (2 * D)
    have hxroot : A + E * x + D * x ^ 2 = 0 := by
      dsimp only [x]
      field_simp [hD]
      linear_combination hr
    have hyroot : A + E * y + D * y ^ 2 = 0 := by
      dsimp only [y]
      field_simp [hD]
      linear_combination hr
    have hxnorm : 1 ≤ ‖x‖ := by
      exact not_lt.mp (fun hx => hstable x hx hxroot)
    have hynorm : 1 ≤ ‖y‖ := by
      exact not_lt.mp (fun hy => hstable y hy hyroot)
    have hxy : x * y = A / D := by
      dsimp only [x, y]
      field_simp [hD]
      linear_combination -hr
    have hratio : 1 ≤ ‖A / D‖ := by
      rw [← hxy, norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hzratio : z = -(A / D) := by
      apply (mul_left_cancel₀ hD)
      rw [mul_neg, mul_div_cancel₀ A hD]
      exact eq_neg_of_add_eq_zero_right hzero
    rw [hzratio, norm_neg] at hz
    exact (not_lt_of_ge hratio) hz

end StatMech.FrontierA
