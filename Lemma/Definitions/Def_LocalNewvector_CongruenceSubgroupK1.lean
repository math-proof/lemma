import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def congruenceK0 (ϖ : R) (n : ℕ) : Subgroup (GL (Fin 2) K) where
  carrier := {x | ∃ y : GL (Fin 2) R,
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n}}
  one_mem' := ⟨1, map_one _, by simp⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
    refine ⟨y₁ * y₂, map_mul _ _ _, ?_⟩
    have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0
        = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 0
          + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 0 := by
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hentry]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  inv_mem' := by
    rintro x ⟨y, rfl, h⟩
    refine ⟨y⁻¹, map_inv _ _, ?_⟩
    have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
        = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
    have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 0
        = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
            * (-(y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
      rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
      simp [smul_eq_mul]
    rw [hco, hadj]
    exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ h)

theorem mem_congruenceK0_iff {ϖ : R} {n : ℕ} {x : GL (Fin 2) K} :
    x ∈ congruenceK0 (K := K) ϖ n ↔
      ∃ y : GL (Fin 2) R,
        Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} :=
  Iff.rfl

theorem congruenceK0_zero (ϖ : R) :
    congruenceK0 (K := K) ϖ 0
      = (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  ext x
  simp [mem_congruenceK0_iff, MonoidHom.mem_range, pow_zero, Ideal.span_singleton_one]

def congruenceK1 (ϖ : R) (n : ℕ) : Subgroup (GL (Fin 2) K) where
  carrier := {x | ∃ y : GL (Fin 2) R,
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} ∧
    (y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1 ∈ Ideal.span {ϖ ^ n}}
  one_mem' := ⟨1, map_one _, by simp, by simp⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨y₁, rfl, hc₁, hd₁⟩ ⟨y₂, rfl, hc₂, hd₂⟩
    refine ⟨y₁ * y₂, map_mul _ _ _, ?_, ?_⟩
    · have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 0
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 0 := by
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hentry]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc₁) (Ideal.mul_mem_left _ _ hc₂)
    · have hentry : ((y₁ * y₂ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 := by
        simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      have hsplit : (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1
          = (y₁ : Matrix (Fin 2) (Fin 2) R) 1 0 * (y₂ : Matrix (Fin 2) (Fin 2) R) 0 1
            + (((y₁ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1) * (y₂ : Matrix (Fin 2) (Fin 2) R) 1 1
              + ((y₂ : Matrix (Fin 2) (Fin 2) R) 1 1 - 1)) := by ring
      rw [hentry, hsplit]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc₁)
        (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hd₁) hd₂)
  inv_mem' := by
    rintro x ⟨y, rfl, hc, hd⟩
    refine ⟨y⁻¹, map_inv _ _, ?_, ?_⟩
    · have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
          = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
      have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 0
          = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
              * (-(y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
        rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
        simp [smul_eq_mul]
      rw [hco, hadj]
      exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ hc)
    · have hco : ((y⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
          = ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ := Matrix.coe_units_inv y
      have hadj : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 1
          = Ring.inverse (y : Matrix (Fin 2) (Fin 2) R).det
              * (y : Matrix (Fin 2) (Fin 2) R) 0 0 := by
        rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
        simp [smul_eq_mul]
      have hone : Ring.inverse ((y : Matrix (Fin 2) (Fin 2) R).det)
          * ((y : Matrix (Fin 2) (Fin 2) R)).det = 1 := by
        refine Ring.inverse_mul_cancel _ ?_
        refine ⟨⟨(y : Matrix (Fin 2) (Fin 2) R).det, (y.inv).det, ?_, ?_⟩, rfl⟩
        · rw [← Matrix.det_mul, y.val_inv, Matrix.det_one]
        · rw [← Matrix.det_mul, y.inv_val, Matrix.det_one]
      have hsplit : ((y : Matrix (Fin 2) (Fin 2) R))⁻¹ 1 1 - 1
          = Ring.inverse ((y : Matrix (Fin 2) (Fin 2) R).det)
              * ((y : Matrix (Fin 2) (Fin 2) R) 0 0
                  * (1 - (y : Matrix (Fin 2) (Fin 2) R) 1 1)
                + (y : Matrix (Fin 2) (Fin 2) R) 0 1
                  * (y : Matrix (Fin 2) (Fin 2) R) 1 0) := by
        rw [hadj]
        rw [Matrix.det_fin_two] at hone ⊢
        linear_combination hone
      rw [hco, hsplit]
      refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ ?_ ?_)
      · have hneg : (1 : R) - (y : Matrix (Fin 2) (Fin 2) R) 1 1
            = -((y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1) := by ring
        rw [hneg]
        exact Ideal.mul_mem_left _ _ (Submodule.neg_mem _ hd)
      · exact Ideal.mul_mem_left _ _ hc

theorem mem_congruenceK1_iff {ϖ : R} {n : ℕ} {x : GL (Fin 2) K} :
    x ∈ congruenceK1 (K := K) ϖ n ↔
      ∃ y : GL (Fin 2) R,
        Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y = x ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ Ideal.span {ϖ ^ n} ∧
        (y : Matrix (Fin 2) (Fin 2) R) 1 1 - 1 ∈ Ideal.span {ϖ ^ n} :=
  Iff.rfl

theorem congruenceK1_le_congruenceK0 (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ congruenceK0 (K := K) ϖ n := by
  rintro x ⟨y, rfl, hc, _⟩
  exact ⟨y, rfl, hc⟩

theorem congruenceK1_zero (ϖ : R) :
    congruenceK1 (K := K) ϖ 0
      = (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  ext x
  simp [mem_congruenceK1_iff, MonoidHom.mem_range, pow_zero, Ideal.span_singleton_one]

theorem congruenceK0_antitone {ϖ : R} {m n : ℕ} (hmn : m ≤ n) :
    congruenceK0 (K := K) ϖ n ≤ congruenceK0 (K := K) ϖ m := by
  rintro x ⟨y, rfl, hc⟩
  exact ⟨y, rfl, Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hc⟩

theorem congruenceK1_antitone {ϖ : R} {m n : ℕ} (hmn : m ≤ n) :
    congruenceK1 (K := K) ϖ n ≤ congruenceK1 (K := K) ϖ m := by
  rintro x ⟨y, rfl, hc, hd⟩
  exact ⟨y, rfl, Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hc,
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ hmn) hd⟩

section Padic

variable (p : ℕ) [Fact p.Prime]

abbrev padicK0 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK0 ((p : ℤ_[p])) n

abbrev padicK1 (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) :=
  congruenceK1 ((p : ℤ_[p])) n

end Padic

end LocalNewvector
