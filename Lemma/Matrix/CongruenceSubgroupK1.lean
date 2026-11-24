module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.LinearCombination
public import Def.LocalNewvector_CongruenceSubgroupK1
public import Abbrev.LocalNewvector_CongruenceSubgroupK1
set_option autoImplicit false


public section

noncomputable section

namespace LocalNewvector

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


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

end Padic

end LocalNewvector

end
