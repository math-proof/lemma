/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard


namespace StatMech.FrontierA

open scoped Matrix


local macro "triangular_minor_det" r:term : term => `(by
  have hrho_local : $r ^ 4 = Complex.I := by assumption
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : $r ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho_local, hI]
  have hrho12 : $r ^ 12 = -Complex.I := by
    rw [show (12 : Nat) = 8 + 4 from rfl, pow_add, hrho8, hrho_local]
    ring
  have hrho9 : $r ^ 9 = -$r := by
    rw [show (9 : Nat) = 8 + 1 from rfl, pow_add, hrho8, pow_one]
    ring
  have hrho10 : $r ^ 10 = -($r ^ 2) := by
    rw [show (10 : Nat) = 8 + 2 from rfl, pow_add, hrho8]
    ring
  have hrho11 : $r ^ 11 = -($r ^ 3) := by
    rw [show (11 : Nat) = 8 + 3 from rfl, pow_add, hrho8]
    ring
  have hrho13 : $r ^ 13 = -($r * Complex.I) := by
    rw [show (13 : Nat) = 12 + 1 from rfl, pow_add, hrho12, pow_one]
    ring
  have hrho14 : $r ^ 14 = -($r ^ 2 * Complex.I) := by
    rw [show (14 : Nat) = 12 + 2 from rfl, pow_add, hrho12]
    ring
  have hrho15 : $r ^ 15 = -($r ^ 3 * Complex.I) := by
    rw [show (15 : Nat) = 12 + 3 from rfl, pow_add, hrho12]
    ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 from rfl, pow_add, hI, pow_one]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    rw [show (5 : Nat) = 4 + 1 from rfl, pow_add, hI4, pow_one, one_mul]
  have hrho5 : $r ^ 5 = $r * Complex.I := by
    rw [show (5 : Nat) = 1 + 4 from rfl, pow_add, hrho_local, pow_one]
  have hrho6 : $r ^ 6 = $r ^ 2 * Complex.I := by
    rw [show (6 : Nat) = 2 + 4 from rfl, pow_add, hrho_local]
  have hrho7 : $r ^ 7 = $r ^ 3 * Complex.I := by
    rw [show (7 : Nat) = 3 + 4 from rfl, pow_add, hrho_local]
  rw [Matrix.det_succ_row_zero]
  simp [triangularKacWardMinor0, triangularKacWardMinor1,
    triangularKacWardMinor2, triangularKacWardMinor3,
    triangularKacWardMinor4, triangularKacWardMinor5,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  try simp only [hrho5, hrho6, hrho7]
  simp only [@Matrix.det_succ_row_zero _ _ 3]
  simp [triangularKacWardMinor0, triangularKacWardMinor1,
    triangularKacWardMinor2, triangularKacWardMinor3,
    triangularKacWardMinor4, triangularKacWardMinor5,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.det_fin_three,
    Fin.succAbove]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring_nf
  try simp only [hrho5, hrho6, hrho7, hrho8, hrho9, hrho10, hrho11,
    hrho12, hrho13, hrho14, hrho15, hI, hI3, hI4, hI5, hrho_local]
  try ring)

end StatMech.FrontierA
