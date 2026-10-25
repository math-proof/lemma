/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Def.StatisticalMechanics.Code.Onsager.KWSpectralSharp.Part3


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem ons_KWmat_eq_arrivalTurn_mul_perm (L : ℕ) [NeZero L] :
    ons_KWmat L 1 ons_turnRoot =
      ons_arrivalTurnMatrix L * (ons_tailDartEquiv L).permMatrix ℂ := by
  ext d2 d1
  rw [Matrix.mul_apply, Finset.sum_eq_single (ons_headDartEquiv L d1)]
  · have htailhead :
        ons_tailDartEquiv L (ons_headDartEquiv L d1) = d1 := by
      exact (ons_headDartEquiv L).symm_apply_apply d1
    have hp : ((ons_tailDartEquiv L).permMatrix ℂ)
        (ons_headDartEquiv L d1) d1 = 1 := by
      simp [Equiv.Perm.permMatrix, htailhead]
    rw [hp, mul_one]
    simp [ons_KWmat, ons_arrivalTurnMatrix, ons_turnMatrix, ons_headDartEquiv]
  · intro dart _ hdart
    by_cases h : ons_tailDartEquiv L dart = d1
    · have : dart = ons_headDartEquiv L d1 := by
        simpa [ons_tailDartEquiv] using congrArg (ons_headDartEquiv L) h
      exact (hdart this).elim
    · have hp : ((ons_tailDartEquiv L).permMatrix ℂ) dart d1 = 0 := by
        simp [Equiv.Perm.permMatrix, h]
      rw [hp, mul_zero]
  · simp

theorem norm_ons_turnMatrix_centered :
    letI : NormedRing (Matrix (Fin 4) (Fin 4) ℂ) :=
      Matrix.instL2OpNormedRing
    ‖ons_turnMatrix ons_turnRoot - 1‖ = Real.sqrt 2 := by
  letI : NormedRing (Matrix (Fin 4) (Fin 4) ℂ) :=
    Matrix.instL2OpNormedRing
  let B := ons_turnMatrix ons_turnRoot - 1
  have hBstar : Bᴴ = B := by
    dsimp [B]
    rw [Matrix.conjTranspose_sub, ons_turnMatrix_turnRoot_isHermitian.eq,
      Matrix.conjTranspose_one]
  have hsq : B * B = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    exact ons_turnMatrix_centered_sq
  have hnormsq : ‖B‖ * ‖B‖ = 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hBstar, hsq]
    norm_num
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
  nlinarith [norm_nonneg B]

theorem norm_ons_arrivalTurnMatrix_centered (L : ℕ) [NeZero L] :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
      Matrix.instL2OpNormedRing
    ‖ons_arrivalTurnMatrix L - 1‖ = Real.sqrt 2 := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    Matrix.instL2OpNormedRing
  let B := ons_arrivalTurnMatrix L - 1
  have hBstar : Bᴴ = B := by
    dsimp [B]
    rw [Matrix.conjTranspose_sub, (ons_arrivalTurnMatrix_isHermitian L).eq,
      Matrix.conjTranspose_one]
  have hsq : B * B = (2 : ℂ) • (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    ons_arrivalTurnMatrix_centered_sq L
  have hnormsq : ‖B‖ * ‖B‖ = 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hBstar, hsq]
    norm_num
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
  nlinarith [norm_nonneg B]

theorem norm_ons_arrivalTurnMatrix_le (L : ℕ) [NeZero L] :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
      Matrix.instL2OpNormedRing
    ‖ons_arrivalTurnMatrix L‖ ≤ Real.sqrt 2 + 1 := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    Matrix.instL2OpNormedRing
  calc
    ‖ons_arrivalTurnMatrix L‖ = ‖(ons_arrivalTurnMatrix L - 1) + 1‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖ons_arrivalTurnMatrix L - 1‖ + ‖(1 : Matrix (ons_Dart L) (ons_Dart L) ℂ)‖ :=
      norm_add_le _ _
    _ = Real.sqrt 2 + 1 := by rw [norm_ons_arrivalTurnMatrix_centered]; simp


theorem norm_ons_KWmat_turnRoot_sharp (L : ℕ) [NeZero L] (x : ℂ) :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
      Matrix.instL2OpNormedRing
    ‖ons_KWmat L x ons_turnRoot‖ ≤ (Real.sqrt 2 + 1) * ‖x‖ := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    Matrix.instL2OpNormedRing
  have hscale : ons_KWmat L x ons_turnRoot = x • ons_KWmat L 1 ons_turnRoot := by
    ext d2 d1
    simp only [ons_KWmat, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hscale, ons_KWmat_eq_arrivalTurn_mul_perm]
  calc
    ‖x • (ons_arrivalTurnMatrix L * (ons_tailDartEquiv L).permMatrix ℂ)‖ =
        ‖x‖ * ‖ons_arrivalTurnMatrix L *
          (ons_tailDartEquiv L).permMatrix ℂ‖ := norm_smul _ _
    _ ≤ ‖x‖ * (‖ons_arrivalTurnMatrix L‖ *
          ‖(ons_tailDartEquiv L).permMatrix ℂ‖) := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ ‖x‖ * ((Real.sqrt 2 + 1) * 1) := by
      gcongr
      · exact norm_ons_arrivalTurnMatrix_le L
      · exact Matrix.permMatrix_l2_opNorm_le _
    _ = (Real.sqrt 2 + 1) * ‖x‖ := by ring

end StatMech.Onsager
