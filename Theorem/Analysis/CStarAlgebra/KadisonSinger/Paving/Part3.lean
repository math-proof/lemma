/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Def.Analysis.CStarAlgebra.KadisonSinger.Paving.Part5
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

lemma ksOperatorNorm_mul {l m n : Type} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    ksOperatorNorm (A * B) ≤ ksOperatorNorm A * ksOperatorNorm B := by
  unfold ksOperatorNorm ksMatrixCLM
  have h := ((Matrix.toEuclideanLin (n := n) (m := m) (𝕜 := ℂ)).trans
    LinearMap.toContinuousLinearMap A).opNorm_comp_le
      ((Matrix.toEuclideanLin (n := l) (m := n) (𝕜 := ℂ)).trans
        LinearMap.toContinuousLinearMap B)
  convert! h
  ext1 x
  exact congr(WithLp.toLp 2 ($(Matrix.toLin'_mul A B) x))

lemma ksOperatorNorm_conjTranspose {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    ksOperatorNorm (Matrix.conjTranspose A) = ksOperatorNorm A := by
  unfold ksOperatorNorm ksMatrixCLM
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    Matrix.toLin_conjTranspose, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

lemma ksBlockEmbedding_star_mul_self {r d : ℕ} (j : Fin r) :
    Matrix.conjTranspose
        (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) * ksBlockEmbedding j =
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext a b
  simp [ksBlockEmbedding, Matrix.mul_apply, Matrix.one_apply, eq_comm]

lemma ksBlockEmbedding_norm_le {r d : ℕ} [Nonempty (Fin d)] (j : Fin r) :
    ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  have hsq : ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ *
      ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ksBlockEmbedding_star_mul_self, norm_one]
  nlinarith [norm_nonneg (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)]

lemma ksBlockCompression_eq {r d : ℕ}
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    Matrix.conjTranspose (ksBlockEmbedding j) * M * ksBlockEmbedding j =
      ksBlock M j := by
  ext a b
  change (∑ x : Fin r × Fin d, (∑ y : Fin r × Fin d,
    star (ksBlockEmbedding j y a) * M y x) * ksBlockEmbedding j x b) = _
  simp [ksBlockEmbedding, ksBlock]

lemma ksBlock_norm_le {r d : ℕ} [Nonempty (Fin d)]
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    ksOperatorNorm (ksBlock M j) ≤ ksOperatorNorm M := by
  rw [← ksBlockCompression_eq M j]
  rw [Matrix.mul_assoc]
  have hE : ksOperatorNorm
      (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) ≤ 1 := by
    unfold ksOperatorNorm ksMatrixCLM
    rw [← Matrix.l2_opNorm_def]
    exact ksBlockEmbedding_norm_le j
  have hM_nonneg : 0 ≤ ksOperatorNorm M := by
    exact norm_nonneg _
  have hE_nonneg : 0 ≤ ksOperatorNorm
      (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) := by
    exact norm_nonneg _
  calc
    ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j) *
        (M * ksBlockEmbedding j)) ≤
        ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) *
          ksOperatorNorm (M * ksBlockEmbedding j) := by
      exact ksOperatorNorm_mul (Matrix.conjTranspose (ksBlockEmbedding j))
        (M * ksBlockEmbedding j)
    _ ≤ ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) *
        (ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j)) :=
      mul_le_mul_of_nonneg_left
        (ksOperatorNorm_mul M (ksBlockEmbedding j))
        (by exact norm_nonneg (ksMatrixCLM (Matrix.conjTranspose (ksBlockEmbedding j))))
    _ = ksOperatorNorm (ksBlockEmbedding j) *
        (ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j)) := by
      rw [show ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) =
          ksOperatorNorm (ksBlockEmbedding j) by
        exact ksOperatorNorm_conjTranspose (ksBlockEmbedding j)]
    _ = (ksOperatorNorm (ksBlockEmbedding j) * ksOperatorNorm M) *
        ksOperatorNorm (ksBlockEmbedding j) := by ring
    _ ≤ ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j) :=
      mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hE hM_nonneg)
        hE_nonneg
    _ ≤ ksOperatorNorm M * 1 :=
      mul_le_mul_of_nonneg_left hE hM_nonneg
    _ = ksOperatorNorm M := mul_one _

lemma ksPavingProj_norm_le {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    ‖ksPavingProj c j‖ ≤ 1 := by
  have hsq : ‖ksPavingProj c j‖ * ‖ksPavingProj c j‖ = ‖ksPavingProj c j‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ksPavingProj_star, ksPavingProj_sq]
  nlinarith [norm_nonneg (ksPavingProj c j)]

lemma ksRefine_order_bound {n r s : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k)
    (hbound : ksPavingProj d k * B * ksPavingProj d k ≤ a • ksPavingProj d k) :
    ksPavingProj c j * B * ksPavingProj c j ≤ a • ksPavingProj c j := by
  let Q := ksPavingProj c j
  let P := ksPavingProj d k
  have hQP : Q * P = Q := ksPavingProj_mul_of_refines c j d k h
  have hPQ : P * Q = Q := ksPavingProj_mul_of_refines' c j d k h
  have hQself : IsSelfAdjoint Q :=
    (show Q.IsHermitian from ksPavingProj_star c j).isSelfAdjoint
  have hc := hQself.conjugate_le_conjugate hbound
  calc
    Q * B * Q = Q * (P * B * P) * Q := by
      rw [show Q * (P * B * P) * Q = (Q * P) * B * (P * Q) by noncomm_ring]
      rw [hQP, hPQ]
    _ ≤ Q * (a • P) * Q := hc
    _ = a • Q := by
      rw [show Q * (a • P) * Q = a • (Q * P * Q) by
        simp only [mul_smul_comm, smul_mul_assoc]]
      rw [hQP, ksPavingProj_sq]

lemma ksCompression_le_smul_projection {n r : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B)
    (c : Fin n → Fin r) (j : Fin r) (a : ℝ)
    (hnorm : ‖ksPavingProj c j * B * ksPavingProj c j‖ ≤ a) :
    ksPavingProj c j * B * ksPavingProj c j ≤ a • ksPavingProj c j := by
  let Q := ksPavingProj c j
  let X := Q * B * Q
  have hQstar : Matrix.conjTranspose Q = Q := ksPavingProj_star c j
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hQself : IsSelfAdjoint Q :=
    (show Q.IsHermitian from hQstar).isSelfAdjoint
  have hX0 : 0 ≤ X := by
    have hx := star_left_conjugate_nonneg hB0 Q
    simpa only [X, Matrix.star_eq_conjTranspose, hQstar] using hx
  have hXleNorm : X ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖X‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self X (IsSelfAdjoint.of_nonneg hX0)
  have hmap : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖X‖ ≤
      (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) a := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right hnorm
      (show 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) from zero_le_one)
  have hc := hQself.conjugate_le_conjugate (hXleNorm.trans hmap)
  change X ≤ a • Q
  calc
    X = Q * X * Q := by
      symm
      calc
        Q * X * Q = (Q * Q) * B * (Q * Q) := by
          simp only [X]
          noncomm_ring
        _ = X := by rw [hQsq]
    _ ≤ Q * (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) a * Q := hc
    _ = a • Q := by simp [Algebra.algebraMap_eq_smul_one, hQsq]

lemma ksMSS_outcome_for_frame
    (hMSS : FiniteMSSBound.{0}) {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : Fin m → Fin r,
      ‖∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
        (star (ksLiftVector (c i) (u i)))‖ ≤
          (1 + Real.sqrt (r * δ)) ^ 2 := by
  apply hMSS m (Fin r × Fin d) (fun _ ↦ r) (fun _ ↦ hr)
    (fun _ _ ↦ (r : ℝ)⁻¹) (fun i a ↦ ksLiftVector a (u i)) (r * δ)
  · positivity
  · intro i a
    positivity
  · intro i
    simp [hr.ne']
  · simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      ksLift_covariance_sum hr u hframe
  · intro i
    calc
      ∑ a : Fin r, (r : ℝ)⁻¹ * ∑ x, ‖ksLiftVector a (u i) x‖ ^ 2 =
          r * ∑ k, ‖u i k‖ ^ 2 := by
        simp_rw [ksLift_norm_sq]
        simp [hr.ne']
      _ ≤ r * δ := mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg r)

end Analysis.CStarAlgebra.KadisonSinger
