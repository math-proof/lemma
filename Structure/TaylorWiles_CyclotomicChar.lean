import Instance.TaylorWiles_Primes
import Mathlib

set_option autoImplicit false

open scoped Pointwise
open scoped commutatorElement

open Matrix MatrixGroups

namespace TaylorWiles

open NumberField FrobeniusDensity Ideal

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

section CycloChar

variable {m : ℕ} [NeZero m] {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m)


end CycloChar

section Frobenius

variable {m : ℕ} [NeZero m]

omit [NumberField L] [IsGalois ℚ L] in


end Frobenius

variable (L) in

structure CyclotomicLevelStructure (p n : ℕ) (S : Finset ℕ) where
  N : Subgroup (L ≃ₐ[ℚ] L)
  commutator_mem : ∀ g h : L ≃ₐ[ℚ] L, ⁅g, h⁆ ∈ N
  congruent : ∀ σ ∈ N, ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]

variable (L) in


end TaylorWiles
