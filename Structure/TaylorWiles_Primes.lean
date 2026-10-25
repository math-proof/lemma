import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Instance.TaylorWiles_Primes

set_option autoImplicit false

namespace Matrix

variable {R : Type*} [CommRing R]


def HasDistinctRationalEigenvalues (M : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∃ α β : R, α ≠ β ∧ M.trace = α + β ∧ M.det = α * β

end Matrix

namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

abbrev ratPrimeIdeal (ℓ : ℕ) : Ideal ℤ := Ideal.span {(ℓ : ℤ)}


variable {L}

omit [IsGalois ℚ L] in


variable (L)

def RealizesCyclicAt (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : Prop :=
  ∃ _ : ℓ.Prime, ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
    (_ : Finite (𝓞 L ⧸ Q)),
    ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)


end FrobeniusDensity

namespace TaylorWiles

open NumberField Ideal FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
variable {𝕜 : Type*} [Field 𝕜]

variable (L) in


variable (ρ : ResidualRep L 𝕜) (p n : ℕ)


structure Seed (S : Finset ℕ) where

  σ : L ≃ₐ[ℚ] L

  regular : (ρ σ).HasDistinctRationalEigenvalues

  congruent : ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]


end TaylorWiles
