/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Def.Analysis.CStarAlgebra.KadisonSinger.Paving.Part3
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

lemma ksSum_lift_outer {r d : ℕ} (hr : 0 < r) (u : Fin d → ℂ)
    (x y : Fin r × Fin d) :
    ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
      (ksLiftVector a u x * star (ksLiftVector a u y))) =
      if x.1 = y.1 then u x.2 * star (u y.2) else 0 := by
  have hcoef : ((r : ℂ)⁻¹ * (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = 1 := by
    calc
      (r : ℂ)⁻¹ * (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) =
          (r : ℂ)⁻¹ * ((Real.sqrt r * Real.sqrt r : ℝ) : ℂ) := by
        push_cast
        ring
      _ = (r : ℂ)⁻¹ * (r : ℂ) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
        norm_num
      _ = 1 := by simp [hr.ne']
  by_cases hxy : x.1 = y.1
  · simp only [ksLiftVector]
    rw [show y.1 = x.1 from hxy.symm]
    have hsum :
        (∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
          ((if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0) *
            star (if x.1 = a then (Real.sqrt r : ℂ) * u y.2 else 0)))) =
          (((r : ℝ)⁻¹ : ℂ) *
            (((Real.sqrt r : ℂ) * u x.2) * star ((Real.sqrt r : ℂ) * u y.2))) := by
      let f : Fin r → ℂ := fun a ↦ (((r : ℝ)⁻¹ : ℂ) *
        ((if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0) *
          star (if x.1 = a then (Real.sqrt r : ℂ) * u y.2 else 0)))
      change (∑ a, f a) = _
      calc
        (∑ a, f a) = f x.1 := by
          apply Finset.sum_eq_single_of_mem x.1 (Finset.mem_univ _)
          intro a ha hax
          have hxa : x.1 ≠ a := Ne.symm hax
          simp [f, hxa]
        _ = _ := by simp [f]
    rw [hsum]
    simp only [map_mul, RCLike.star_def, Complex.conj_ofReal]
    calc
      (↑r)⁻¹ * ((↑√↑r * u x.2) * (↑√↑r * (starRingEnd ℂ) (u y.2))) =
          (((↑r)⁻¹ * ↑√↑r * ↑√↑r) * (u x.2 * (starRingEnd ℂ) (u y.2))) := by
        ring
      _ = u x.2 * (starRingEnd ℂ) (u y.2) := by rw [hcoef, one_mul]
  · simp only [hxy, ↓reduceIte, ksLiftVector]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hxa : x.1 = a
    · have hya : y.1 ≠ a := fun h ↦ hxy (hxa.trans h.symm)
      simp [hxa, hya]
    · simp [hxa]

lemma ksLift_covariance_sum {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1) :
    ((∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) •
      Matrix.vecMulVec (ksLiftVector a (u i)) (star (ksLiftVector a (u i))))) :
        Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) = 1 := by
  apply funext
  intro x
  apply funext
  intro y
  change ksMatrixEntryLM x y
      (∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) •
        Matrix.vecMulVec (ksLiftVector a (u i)) (star (ksLiftVector a (u i))))) =
    ksMatrixEntryLM x y (1 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ)
  simp only [map_sum, map_smul]
  change (∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
    (ksLiftVector a (u i) x * star (ksLiftVector a (u i) y)))) =
      (1 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) x y
  rw [Matrix.one_apply]
  simp_rw [ksSum_lift_outer hr]
  have hf := congrArg (ksMatrixEntryLM x.2 y.2) hframe
  simp only [map_sum] at hf
  change (∑ i, u i x.2 * star (u i y.2)) =
    (1 : Matrix (Fin d) (Fin d) ℂ) x.2 y.2 at hf
  rw [Matrix.one_apply] at hf
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ↓reduceIte]
    simpa [Prod.ext_iff, hxy] using hf
  · simp [Prod.ext_iff, hxy]

lemma ksLift_norm_sq {r d : ℕ} (a : Fin r) (u : Fin d → ℂ) :
    ∑ x : Fin r × Fin d, ‖ksLiftVector a u x‖ ^ 2 =
      r * ∑ k, ‖u k‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  let f : Fin r → ℝ := fun b ↦ ∑ k, ‖ksLiftVector a u (b, k)‖ ^ 2
  change (∑ b, f b) = _
  calc
    (∑ b, f b) = f a := by
      apply Finset.sum_eq_single_of_mem a (Finset.mem_univ _)
      intro b hb hba
      simp [f, ksLiftVector, hba]
    _ = r * ∑ k, ‖u k‖ ^ 2 := by
      simp only [f, ksLiftVector, ite_true, norm_mul, Complex.norm_real]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      simp_rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
      rw [Finset.mul_sum]

end Analysis.CStarAlgebra.KadisonSinger
