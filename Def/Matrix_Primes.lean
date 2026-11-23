module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Instance.TaylorWiles_Primes
public import Structure.TaylorWiles_Primes
public import Abbrev.TaylorWiles_Primes

@[expose] public section

set_option autoImplicit false


namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]


variable {L}

omit [IsGalois ℚ L] in

variable (L)


def Statement : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ), ∃ ℓ : ℕ, ℓ ∉ S ∧ RealizesCyclicAt L σ ℓ

end FrobeniusDensity

namespace TaylorWiles

open NumberField Ideal FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
variable {𝕜 : Type*} [Field 𝕜]

def IsTaylorWilesPrime (q : ℕ) : Prop :=
  q.Prime ∧ q ≡ 1 [MOD p ^ n] ∧
    ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal q))
      (_ : Finite (𝓞 L ⧸ Q)),
      (ρ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).HasDistinctRationalEigenvalues


def SeedExists (S : Finset ℕ) : Prop := Nonempty (Seed ρ p n S)

end TaylorWiles

end
