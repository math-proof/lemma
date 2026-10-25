/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Macro.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard


namespace StatMech.FrontierA

open scoped Matrix


set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor0_det
    (d1 d2 d3 d4 d5 rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor0 d1 d2 d3 d4 d5 rho).det =
      -d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 + 4 * d1 * d3 * d4 +
        d1 * d4 * d5 - d1 + d2 * d3 * d4 * d5 + d2 * d3 * d4 +
        d2 * d3 * d5 + d2 * d3 + d2 * d4 * d5 - d2 + d3 * d4 * d5 -
        d3 + d4 * d5 - d4 - d5 + 1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : rho ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho, hI]
  have hrho12 : rho ^ 12 = -Complex.I := by
    rw [show (12 : Nat) = 8 + 4 from rfl, pow_add, hrho8, hrho]
    ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 from rfl, pow_add, hI, pow_one]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    rw [show (5 : Nat) = 4 + 1 from rfl, pow_add, hI4, pow_one, one_mul]
  have hrho5 : rho ^ 5 = rho * Complex.I := by
    rw [show (5 : Nat) = 1 + 4 from rfl, pow_add, hrho, pow_one]
  have hrho6 : rho ^ 6 = rho ^ 2 * Complex.I := by
    rw [show (6 : Nat) = 2 + 4 from rfl, pow_add, hrho]
  have hrho7 : rho ^ 7 = rho ^ 3 * Complex.I := by
    rw [show (7 : Nat) = 3 + 4 from rfl, pow_add, hrho]
  rw [triangularKacWardMinor0, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  simp only [hrho5, hrho6, hrho7]
  simp only [@Matrix.det_succ_row_zero _ _ 3]
  simp [Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.det_fin_three,
    Fin.succAbove]
  ring_nf
  rw [hrho8, hrho12, hI3, hI4, hI5, hrho]
  ring_nf
  rw [hI]
  ring

set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor1_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor1 d1 d2 d3 d4 d5 rho).det =
      rho ^ 4 *
        (-d1 * d2 * d3 * d4 + d1 * d2 * d3 * d5 - d1 * d2 * d4 * d5 +
          d1 * d2 + d1 * d3 * d4 * d5 - d1 * d3 + d1 * d4 - d1 * d5) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor2_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor2 d1 d2 d3 d4 d5 rho).det =
      rho ^ 6 *
        (d1 * d2 * d3 * d4 * d5 - 2 * d1 * d2 * d3 * d4 +
          d1 * d2 * d3 - d1 * d2 * d4 * d5 + d1 * d2 -
          d2 * d3 * d4 * d5 + d2 * d3 - d2 * d4 * d5 + 2 * d2 * d5 - d2) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor3_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor3 d1 d2 d3 d4 d5 rho).det =
      rho ^ 2 *
        (-d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 + d1 * d3 * d4 * d5 +
          2 * d1 * d3 * d4 + d1 * d3 + d2 * d3 * d4 * d5 +
          2 * d2 * d3 * d5 + d2 * d3 + d3 * d4 * d5 - d3) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor4_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor4 d1 d2 d3 d4 d5 rho).det =
      rho ^ 7 *
        (-d1 * d2 * d3 * d4 * d5 + d1 * d2 * d3 * d4 +
          2 * d1 * d3 * d4 + d1 * d4 * d5 + d1 * d4 +
          d2 * d3 * d4 * d5 + d2 * d3 * d4 + 2 * d2 * d4 * d5 +
          d4 * d5 - d4) :=
  triangular_minor_det rho

set_option maxHeartbeats 500000 in

theorem triangularKacWardMinor5_det
    (d1 d2 d3 d4 d5 rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    (triangularKacWardMinor5 d1 d2 d3 d4 d5 rho).det =
      rho ^ 3 *
        (d1 * d2 * d3 * d4 * d5 - d1 * d2 * d3 * d5 -
          2 * d1 * d3 * d4 * d5 + d1 * d4 * d5 + d1 * d5 -
          d2 * d3 * d4 * d5 - d2 * d3 * d5 + 2 * d2 * d5 +
          d4 * d5 - d5) :=
  triangular_minor_det rho

set_option maxHeartbeats 1000000 in

theorem triangularKacWardTurnMatrix_diagonal_det
    (d0 d1 d2 d3 d4 d5 rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    (1 - Matrix.diagonal ![d0, d1, d2, d3, d4, d5] *
      triangularKacWardTurnMatrix rho).det =
      1 - (d0 + d1 + d2 + d3 + d4 + d5) +
        (d0 * d1 + d2 * d3 + d4 * d5) +
        d0 * d1 * (d2 + d3 + d4 + d5) +
        d2 * d3 * (d0 + d1 + d4 + d5) +
        d4 * d5 * (d0 + d1 + d2 + d3) +
        4 * (d0 * d2 * d5 + d1 * d3 * d4) +
        (d0 * d1 * d2 * d3 + d0 * d1 * d4 * d5 +
          d2 * d3 * d4 * d5) -
        (d1 * d2 * d3 * d4 * d5 + d0 * d2 * d3 * d4 * d5 +
          d0 * d1 * d3 * d4 * d5 + d0 * d1 * d2 * d4 * d5 +
          d0 * d1 * d2 * d3 * d5 + d0 * d1 * d2 * d3 * d4) +
        d0 * d1 * d2 * d3 * d4 * d5 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrho8 : rho ^ 8 = -1 := by
    rw [show (8 : Nat) = 4 * 2 from rfl, pow_mul, hrho, hI]
  change (triangularKacWardDiagonalSymbol d0 d1 d2 d3 d4 d5 rho).det = _
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by rfl,
    show Fin.succ (Fin.succ (2 : Fin 4)) = (4 : Fin 6) by rfl,
    show Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) = (5 : Fin 6) by rfl]
  rw [triangularKacWardDiagonalSymbol_submatrix0,
    triangularKacWardDiagonalSymbol_submatrix1,
    triangularKacWardDiagonalSymbol_submatrix2,
    triangularKacWardDiagonalSymbol_submatrix3,
    triangularKacWardDiagonalSymbol_submatrix4,
    triangularKacWardDiagonalSymbol_submatrix5,
    triangularKacWardMinor0_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor1_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor2_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor3_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor4_det _ _ _ _ _ _ hrho,
    triangularKacWardMinor5_det _ _ _ _ _ _ hrho]
  simp [triangularKacWardDiagonalSymbol, triangularKacWardTurnMatrix,
    Fin.succAbove]
  ring_nf
  rw [hrho8]
  ring


theorem triangularKacWardSymbolMatrix_det
    (t1 t2 t3 rho z1 z2 z3 : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0)
    (hzsum : z3 = z1 * z2) :
    (triangularKacWardSymbolMatrix t1 t2 t3 rho z1 z2 z3).det =
      (1 + t1 ^ 2) * (1 + t2 ^ 2) * (1 + t3 ^ 2) +
        8 * t1 * t2 * t3 -
        t1 * (1 - t2 ^ 2) * (1 - t3 ^ 2) * (z1 + z1⁻¹) -
        t2 * (1 - t1 ^ 2) * (1 - t3 ^ 2) * (z2 + z2⁻¹) -
        t3 * (1 - t1 ^ 2) * (1 - t2 ^ 2) * (z3 + z3⁻¹) := by
  subst z3
  rw [triangularKacWardSymbolMatrix, triangularKacWardWeightDiagonal,
    triangularKacWardTurnMatrix_diagonal_det _ _ _ _ _ _ _ hrho]
  field_simp [hz1, hz2, hz3]
  ring

end StatMech.FrontierA
