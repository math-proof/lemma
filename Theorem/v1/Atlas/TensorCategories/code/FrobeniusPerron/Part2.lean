/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part3
set_option maxHeartbeats 400000


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

namespace PerronFrobeniusFin2

open FusionRing

noncomputable section

/-- The discriminant `pfDiscriminant M` of a strictly positive 2×2
matrix is positive. -/
lemma pfDiscriminant_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfDiscriminant M := by
  unfold pfDiscriminant
  nlinarith [sq_nonneg (M 0 0 - M 1 1), hM 0 1, hM 1 0]

/-- The Perron–Frobenius eigenvalue of a strictly positive 2×2 matrix
is positive. -/
lemma pfEigenvalue_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfEigenvalue M := by
  unfold pfEigenvalue
  linarith [pfDiscriminant_pos M hM |> Real.sqrt_pos_of_pos, hM 0 0, hM 1 1]

/-- For a strictly positive 2×2 matrix,
`M 0 0 - M 1 1 < sqrt(pfDiscriminant M)`. -/
lemma sqrt_disc_gt_diff (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M 0 0 - M 1 1 < Real.sqrt (pfDiscriminant M) := by
  have hΔ := pfDiscriminant_pos M hM
  have hΔ_ge : (M 0 0 - M 1 1) ^ 2 < pfDiscriminant M := by
    unfold pfDiscriminant; nlinarith [hM 0 1, hM 1 0]
  by_cases h : 0 ≤ M 0 0 - M 1 1
  · calc M 0 0 - M 1 1 = Real.sqrt ((M 0 0 - M 1 1) ^ 2) := (Real.sqrt_sq h).symm
      _ < Real.sqrt (pfDiscriminant M) := Real.sqrt_lt_sqrt (sq_nonneg _) hΔ_ge
  · linarith [Real.sqrt_pos_of_pos hΔ]

/-- The explicit eigenvector `pfEigenvec M` has strictly positive
entries when `M` does. -/
lemma pfEigenvec_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    ∀ i, 0 < pfEigenvec M i := by
  intro i; fin_cases i
  · show 0 < (pfEigenvec M) 0
    simp [pfEigenvec, Matrix.cons_val_zero]; exact hM 0 1
  · show 0 < (pfEigenvec M) 1
    simp [pfEigenvec, Matrix.cons_val_one]
    unfold pfEigenvalue; linarith [sqrt_disc_gt_diff M hM]

/-- `pfEigenvalue M` is a root of the characteristic polynomial of `M`. -/
lemma pfEigenvalue_char_poly (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    pfEigenvalue M ^ 2 - (M 0 0 + M 1 1) * pfEigenvalue M +
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
  unfold pfEigenvalue pfDiscriminant
  have hΔ : 0 ≤ pfDiscriminant M := le_of_lt (pfDiscriminant_pos M hM)
  unfold pfDiscriminant at hΔ
  nlinarith [Real.sq_sqrt hΔ]

/-- `pfEigenvec M` is an eigenvector of `M` with eigenvalue
`pfEigenvalue M`. -/
lemma pfEigenvec_is_eigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M.mulVec (pfEigenvec M) = pfEigenvalue M • pfEigenvec M := by
  ext i; fin_cases i
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]; ring
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    nlinarith [pfEigenvalue_char_poly M hM]

/-- Uniqueness of positive eigenvectors of a strictly positive 2×2
matrix up to scaling. -/
lemma pfUnique_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : Fin 2 → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by
  have hv0 := hv 0; have hv1 := hv 1; have hw0 := hw 0; have hw1 := hw 1
  have hv0_ne : v 0 ≠ 0 := ne_of_gt hv0
  have hv1_ne : v 1 ≠ 0 := ne_of_gt hv1
  have hw0_ne : w 0 ≠ 0 := ne_of_gt hw0
  have hw1_ne : w 1 ≠ 0 := ne_of_gt hw1

  have hrv0 : M 0 0 * v 0 + M 0 1 * v 1 = r₁ * v 0 := by
    have := congr_fun hev 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrv1 : M 1 0 * v 0 + M 1 1 * v 1 = r₁ * v 1 := by
    have := congr_fun hev 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw0 : M 0 0 * w 0 + M 0 1 * w 1 = r₂ * w 0 := by
    have := congr_fun hew 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw1 : M 1 0 * w 0 + M 1 1 * w 1 = r₂ * w 1 := by
    have := congr_fun hew 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith

  have hv_01 : (r₁ - M 0 0) * v 0 = M 0 1 * v 1 := by linarith
  have hv_10 : (r₁ - M 1 1) * v 1 = M 1 0 * v 0 := by linarith
  have hw_01 : (r₂ - M 0 0) * w 0 = M 0 1 * w 1 := by linarith

  have hr1_gt0 : M 0 0 < r₁ := by nlinarith [hM 0 1]
  have hr1_gt1 : M 1 1 < r₁ := by nlinarith [hM 1 0]
  have hr2_gt0 : M 0 0 < r₂ := by nlinarith [hM 0 1]
  have hr2_gt1 : M 1 1 < r₂ := by nlinarith [hM 1 0]

  have hcp1 : (r₁ - M 0 0) * (r₁ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₁ - M 0 0 = M 0 1 * v 1 / v 0 := by field_simp; linarith
    have hd : r₁ - M 1 1 = M 1 0 * v 0 / v 1 := by field_simp; linarith
    rw [ha, hd]; field_simp
  have hcp2 : (r₂ - M 0 0) * (r₂ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₂ - M 0 0 = M 0 1 * w 1 / w 0 := by field_simp; linarith
    have hd : r₂ - M 1 1 = M 1 0 * w 0 / w 1 := by field_simp; linarith
    rw [ha, hd]; field_simp

  have hfact : (r₁ - r₂) * (r₁ + r₂ - (M 0 0 + M 1 1)) = 0 := by nlinarith

  have hr_eq : r₁ = r₂ := by
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · exfalso; linarith

  rw [hr_eq] at hv_01

  have h_rne : r₂ - M 0 0 ≠ 0 := by linarith
  have hcross_eq : (r₂ - M 0 0) * (v 0 * w 1 - w 0 * v 1) = 0 := by
    have l1 : (r₂ - M 0 0) * v 0 * w 1 = M 0 1 * v 1 * w 1 := by
      have := congr_arg (· * w 1) hv_01; simp [mul_assoc] at this; linarith
    have l2 : (r₂ - M 0 0) * w 0 * v 1 = M 0 1 * w 1 * v 1 := by
      have := congr_arg (· * v 1) hw_01; simp [mul_assoc] at this; linarith
    linarith [mul_comm (v 1) (w 1)]

  have hcross : v 0 * w 1 = w 0 * v 1 := by
    rcases mul_eq_zero.mp hcross_eq with h | h
    · exact absurd h h_rne
    · linarith

  refine ⟨w 0 / v 0, ?_⟩
  intro i; fin_cases i
  · show w 0 = w 0 / v 0 * v 0
    rw [div_mul_cancel₀ _ hv0_ne]
  · show w 1 = w 0 / v 0 * v 1
    rw [div_mul_eq_mul_div, ← hcross, mul_div_cancel_left₀ _ hv0_ne]

end
end PerronFrobeniusFin2
end FusionRing
