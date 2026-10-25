/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Def.Analysis.CStarAlgebra.KadisonSinger.Paving.Part4
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

lemma ksFiltered_columns {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → Fin r) (j : Fin r) :
    ((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
      Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) :
        Matrix (Fin n) (Fin n) ℂ) =
      S * ksPavingProj c j * Matrix.conjTranspose S := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM a b
      (∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) =
    ksMatrixEntryLM a b (S * ksPavingProj c j * Matrix.conjTranspose S)
  simp only [map_sum, ksMatrixEntryLM]
  change (∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), S a i * star (S b i)) =
    (S * ksPavingProj c j * Matrix.conjTranspose S) a b
  have hinner (i : Fin n) :
      (S * ksPavingProj c j) a i = S a i * (if c i = j then 1 else 0) := by
    simp [ksPavingProj]
  rw [Matrix.mul_apply]
  simp_rw [hinner]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : c i = j <;> simp [hc]

lemma ksAll_columns {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) :
      Matrix (Fin n) (Fin n) ℂ) = S * Matrix.conjTranspose S := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM a b
      (∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) =
    ksMatrixEntryLM a b (S * Matrix.conjTranspose S)
  simp only [map_sum, ksMatrixEntryLM]
  change (∑ i, S a i * star (S b i)) = (S * Matrix.conjTranspose S) a b
  rw [Matrix.mul_apply]
  simp

lemma ksColumn_norm_sq {n : ℕ} (S B : Matrix (Fin n) (Fin n) ℂ)
    (hSB : Matrix.conjTranspose S * S = B) (i : Fin n) :
    ((∑ k, ‖S k i‖ ^ 2 : ℝ) : ℂ) = B i i := by
  have hi := congrFun (congrFun hSB i) i
  simpa [Matrix.mul_apply, RCLike.star_def, RCLike.conj_mul] using hi

lemma ksPavingProj_star {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    Matrix.conjTranspose (ksPavingProj c j) = ksPavingProj c j := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [ksPavingProj, Matrix.conjTranspose_apply]
  · simp [ksPavingProj, Matrix.conjTranspose_apply, hab, Ne.symm hab]

lemma ksPavingProj_sq {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    ksPavingProj c j * ksPavingProj c j = ksPavingProj c j := by
  rw [show ksPavingProj c j = Matrix.diagonal (fun i ↦ if c i = j then 1 else 0) by rfl]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j <;> simp [hc]

lemma ksPavingProj_mul_of_refines {n r s : ℕ}
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k) :
    ksPavingProj c j * ksPavingProj d k = ksPavingProj c j := by
  simp only [ksPavingProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j
  · simp [hc, h i hc]
  · simp [hc]

lemma ksPavingProj_mul_of_refines' {n r s : ℕ}
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k) :
    ksPavingProj d k * ksPavingProj c j = ksPavingProj c j := by
  simp only [ksPavingProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j
  · simp [hc, h i hc]
  · simp [hc]

end Analysis.CStarAlgebra.KadisonSinger
