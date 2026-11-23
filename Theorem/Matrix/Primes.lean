module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Instance.TaylorWiles_Primes
public import Structure.TaylorWiles_Primes
public import Abbrev.TaylorWiles_Primes

public section

set_option autoImplicit false

namespace Matrix

variable {R : Type*} [CommRing R]

public theorem sq_eq_trace_smul_sub_det_smul_one (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring


public theorem pow_add_two_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one, Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]


public theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]


end Matrix

namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]


public theorem ratPrimeIdeal_ne_bot {ℓ : ℕ} (hℓ : ℓ.Prime) : ratPrimeIdeal ℓ ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ.ne_zero

variable {L}

omit [IsGalois ℚ L] in


public theorem finite_quotient_of_ne_bot {Q : Ideal (𝓞 L)} (hQ : Q ≠ ⊥) : Finite (𝓞 L ⧸ Q) :=
  Ring.HasFiniteQuotients.finiteQuotient hQ

omit [IsGalois ℚ L] in


public theorem ne_bot_of_liesOver_ratPrimeIdeal {ℓ : ℕ} (hℓ : ℓ.Prime) {Q : Ideal (𝓞 L)}
    [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (ratPrimeIdeal_ne_bot hℓ) Q

variable (L)


