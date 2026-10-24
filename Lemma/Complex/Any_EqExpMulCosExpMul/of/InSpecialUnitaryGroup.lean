import Mathlib
import sympy.Basic
open Complex
open Matrix


/-- ported from external source -/

private lemma  exp_mul_exp (u v : ℝ) : Complex.exp (u * I) * Complex.exp (v * I) = Complex.exp (((u + v : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma  exp_neg_mul_exp (u v : ℝ) : Complex.exp (-(u * I)) * Complex.exp (v * I) = Complex.exp (((v - u : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma  exp_mul_exp_neg (u v : ℝ) : Complex.exp (u * I) * Complex.exp (-(v * I)) = Complex.exp (-(((v - u : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma  exp_neg_mul_exp_neg (u v : ℝ) :
  Complex.exp (-(u * I)) * Complex.exp (-(v * I)) = Complex.exp (-(((u + v : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma  conj_ofReal_mul_exp (x θ : ℝ) :
  (starRingEnd ℂ) ((x : ℂ) * Complex.exp (θ * I)) = (x : ℂ) * Complex.exp (-((θ : ℂ) * I)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 2; ring

private lemma helper_main (k : Matrix (Fin 2) (Fin 2) ℂ) (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
  ∃ a b c : ℝ,
    k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
          !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
          !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))] := by
  obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hk
  rw [Matrix.mem_unitaryGroup_iff] at hU
  have e1 : k 0 0 * (starRingEnd ℂ) (k 0 0) + k 0 1 * (starRingEnd ℂ) (k 0 1) = 1 := by
    have h := congrFun (congrFun hU 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using h
  have e2 : k 1 0 * (starRingEnd ℂ) (k 1 0) + k 1 1 * (starRingEnd ℂ) (k 1 1) = 1 := by
    have h := congrFun (congrFun hU 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using h
  have e3 : k 0 0 * (starRingEnd ℂ) (k 1 0) + k 0 1 * (starRingEnd ℂ) (k 1 1) = 0 := by
    have h := congrFun (congrFun hU 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using h
  have e4 : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by rwa [← Matrix.det_fin_two]
  have e3' : (starRingEnd ℂ) (k 0 0) * k 1 0 + (starRingEnd ℂ) (k 0 1) * k 1 1 = 0 := by
    have h := congrArg (starRingEnd ℂ) e3
    simpa [map_add, map_mul, Complex.conj_conj] using h
  have hs : k 1 1 = (starRingEnd ℂ) (k 0 0) := by
    linear_combination (starRingEnd ℂ) (k 0 0) * e4 + k 0 1 * e3' - k 1 1 * e1
  have hq : k 0 1 = -(starRingEnd ℂ) (k 1 0) := by
    linear_combination (-(starRingEnd ℂ) (k 1 0)) * e4 - k 0 1 * e2 + k 1 1 * e3
  have hnorm : ‖k 0 0‖ ^ 2 + ‖k 1 0‖ ^ 2 = 1 := by
    have h1 : k 0 0 * (starRingEnd ℂ) (k 0 0) + k 1 0 * (starRingEnd ℂ) (k 1 0) = 1 := by
      have : k 0 1 * (starRingEnd ℂ) (k 0 1) = k 1 0 * (starRingEnd ℂ) (k 1 0) := by
        rw [hq, map_neg, Complex.conj_conj]; ring
      rwa [← this]
    rw [Complex.mul_conj, Complex.mul_conj] at h1
    have h2 : ((Complex.normSq (k 0 0) + Complex.normSq (k 1 0) : ℝ) : ℂ) = 1 := by push_cast; exact h1
    have h3 : Complex.normSq (k 0 0) + Complex.normSq (k 1 0) = 1 := by exact_mod_cast h2
    rwa [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h3
  have hp1 : ‖k 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (k 0 0), norm_nonneg (k 1 0)]
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.arccos ‖k 0 0‖ := ⟨_, rfl⟩
  have hcos : Real.cos b = ‖k 0 0‖ := by
    rw [hb]; apply Real.cos_arccos (by linarith [norm_nonneg (k 0 0)]) hp1
  have hsin : Real.sin b = ‖k 1 0‖ := by
    rw [hb, Real.sin_arccos]
    have : 1 - ‖k 0 0‖ ^ 2 = ‖k 1 0‖ ^ 2 := by linarith
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Complex.arg (k 0 0) := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Complex.arg (k 1 0) := ⟨_, rfl⟩
  have hpθ : (‖k 0 0‖ : ℂ) * Complex.exp (θ * I) = k 0 0 := by rw [hθ]; apply Complex.norm_mul_exp_arg_mul_I _
  have hrφ : (‖k 1 0‖ : ℂ) * Complex.exp (φ * I) = k 1 0 := by rw [hφ]; apply Complex.norm_mul_exp_arg_mul_I _
  refine ⟨(θ - φ) / 2, b, (θ + φ) / 2, ?_⟩
  have h00 : Complex.exp ((((θ - φ) / 2 : ℝ) : ℂ) * I) * (Real.cos b : ℂ) * Complex.exp ((((θ + φ) / 2 : ℝ) : ℂ) * I) = k 0 0 := by
    rw [hcos, mul_right_comm, exp_mul_exp, show (θ - φ) / 2 + (θ + φ) / 2 = θ by ring, mul_comm, hpθ]
  have h10 : Complex.exp (-((((θ - φ) / 2 : ℝ) : ℂ) * I)) * (Real.sin b : ℂ) * Complex.exp ((((θ + φ) / 2 : ℝ) : ℂ) * I) = k 1 0 := by
    rw [hsin, mul_right_comm, exp_neg_mul_exp, show (θ + φ) / 2 - (θ - φ) / 2 = φ by ring, mul_comm, hrφ]
  have h01 : Complex.exp ((((θ - φ) / 2 : ℝ) : ℂ) * I) * (-(Real.sin b : ℂ)) * Complex.exp (-((((θ + φ) / 2 : ℝ) : ℂ) * I)) = k 0 1 := by
    rw [hq, ← hrφ, conj_ofReal_mul_exp, hsin, mul_neg, neg_mul, mul_right_comm, exp_mul_exp_neg,
      show (θ + φ) / 2 - (θ - φ) / 2 = φ by ring, mul_comm]
  have h11 : Complex.exp (-((((θ - φ) / 2 : ℝ) : ℂ) * I)) * (Real.cos b : ℂ) * Complex.exp (-((((θ + φ) / 2 : ℝ) : ℂ) * I)) = k 1 1 := by
    rw [hs, ← hpθ, conj_ofReal_mul_exp, hcos, mul_right_comm, exp_neg_mul_exp_neg,
      show (θ - φ) / 2 + (θ + φ) / 2 = θ by ring, mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simpa using h00.symm
  · simpa using h01.symm
  · simpa using h10.symm
  · simpa using h11.symm
@[path]
private lemma main
  {k : Matrix (Fin 2) (Fin 2) ℂ}
-- given
  (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
-- imply
  ∃ a b c : ℝ,
      k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
            !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
            !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))] :=
  helper_main k hk


-- created on 2026-10-23
