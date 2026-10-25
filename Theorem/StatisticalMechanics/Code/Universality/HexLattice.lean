/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


@[simp]
theorem norm_hexUnit (h : ℤ) : ‖hexUnit h‖ = 1 := by
  unfold hexUnit
  rw [Complex.norm_exp]
  simp [Complex.mul_re]


theorem hexUnit_ne_zero (h : ℤ) : hexUnit h ≠ 0 := by
  intro hz
  have := norm_hexUnit h
  rw [hz] at this
  simp at this


theorem hexUnit_zero : hexUnit 0 = Complex.exp (Complex.I * (Real.pi / 6)) := by
  unfold hexUnit; norm_num

theorem hexUnit_one : hexUnit 1 = Complex.exp (Complex.I * (Real.pi / 2)) := by
  unfold hexUnit
  congr 1
  push_cast
  ring

theorem hexUnit_two : hexUnit 2 = Complex.exp (Complex.I * (5 * Real.pi / 6)) := by
  unfold hexUnit
  congr 1
  push_cast
  ring


theorem hexUnit_add_three (h : ℤ) : hexUnit (h + 3) = - hexUnit h := by
  unfold hexUnit
  have hsplit : Complex.I * (Real.pi / 6 + ((h + 3 : ℤ) : ℝ) * (Real.pi / 3))
      = Complex.I * (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
  ring


end StatMech.Universality
