/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Spectrum

open Matrix

namespace LeastSquares

/-- For a real square matrix, the transpose equals the star (since conjugation is trivial on `ℝ`). -/
lemma transpose_eq_star_real {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : X.transpose = star X := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- Predicate stating that `B` is the Moore–Penrose pseudoinverse of `A`. It encodes the
four classical Penrose conditions: `A B A = A`, `B A B = B`, `A B` is symmetric, and
`B A` is symmetric. -/
structure IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop where
  mul_pinv_mul : A * B * A = A
  pinv_mul_pinv : B * A * B = B
  mul_pinv_symmetric : (A * B).transpose = A * B
  pinv_mul_symmetric : (B * A).transpose = B * A

/-- Every real matrix admits a Moore–Penrose pseudoinverse, constructed via the spectral
decomposition of `Aᵀ A`. -/
lemma exists_moorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ∃ B : Matrix n m ℝ, IsMoorePenrosePseudoinverse A B := by
  set H := A.conjTranspose * A with hH_def
  have hH : H.IsHermitian := isHermitian_conjTranspose_mul_self A
  set φ : Matrix n n ℝ ≃⋆ₐ[ℝ] Matrix n n ℝ :=
    Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hH.eigenvectorUnitary
  set D := diagonal hH.eigenvalues with hD_def
  set D_inv := diagonal (fun i => (hH.eigenvalues i)⁻¹) with hDinv_def
  set H_pinv := φ D_inv with hHpinv_def

  have hD_eq : diagonal (RCLike.ofReal ∘ hH.eigenvalues) = D := by
    simp [hD_def, RCLike.ofReal_real_eq_id]
  have hH_eq : H = φ D := by rw [hH.spectral_theorem, hD_eq]
  refine ⟨H_pinv * A.conjTranspose, ?_⟩

  have h1H : H * H_pinv * H = H := by
    rw [hH_eq, hHpinv_def, ← map_mul, ← map_mul]; congr 1
    simp only [hD_def, hDinv_def, diagonal_mul_diagonal]
    congr 1; ext i; by_cases h : hH.eigenvalues i = 0 <;> simp [h]

  have h2H : H_pinv * H * H_pinv = H_pinv := by
    rw [hH_eq, hHpinv_def, ← map_mul, ← map_mul]; congr 1
    simp only [hD_def, hDinv_def, diagonal_mul_diagonal]
    congr 1; ext i; by_cases h : hH.eigenvalues i = 0 <;> simp [h]

  have h4H : (H_pinv * H).transpose = H_pinv * H := by
    rw [hH_eq, hHpinv_def, transpose_eq_star_real, ← map_mul, ← map_star φ,
      ← transpose_eq_star_real]
    congr 1; simp only [hDinv_def, hD_def, diagonal_mul_diagonal, diagonal_transpose]

  have h_sym : H_pinv.transpose = H_pinv := by
    rw [transpose_eq_star_real, hHpinv_def, ← map_star φ, ← transpose_eq_star_real,
      hDinv_def, diagonal_transpose]

  have h_A_proj : A * H_pinv * H = A := by
    have h_ker : A * (1 - H_pinv * H) = 0 := by
      rw [← conjTranspose_mul_self_mul_eq_zero, ← hH_def,
        Matrix.mul_sub, Matrix.mul_one,
        show H * (H_pinv * H) = H * H_pinv * H from (Matrix.mul_assoc H H_pinv H).symm,
        h1H, sub_self]
    rw [Matrix.mul_sub, Matrix.mul_one] at h_ker
    rw [Matrix.mul_assoc A H_pinv H]
    exact (eq_of_sub_eq_zero h_ker).symm
  constructor

  · rw [Matrix.mul_assoc, Matrix.mul_assoc H_pinv, ← hH_def, ← Matrix.mul_assoc, h_A_proj]

  · rw [Matrix.mul_assoc H_pinv A.conjTranspose A, ← hH_def,
      ← Matrix.mul_assoc (H_pinv * H) H_pinv A.conjTranspose, h2H]

  · simp only [transpose_mul, h_sym, transpose_transpose,
      conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

  · have : H_pinv * A.conjTranspose * A = H_pinv * H := by
      rw [Matrix.mul_assoc, hH_def]
    rw [this, h4H, ← this]

/-- The Moore–Penrose pseudoinverse `A†` of a real square matrix `A`, obtained by choice
from `exists_moorePenrosePseudoinverse`. -/
noncomputable def moorePenrosePseudoinverse {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (exists_moorePenrosePseudoinverse A).choose
