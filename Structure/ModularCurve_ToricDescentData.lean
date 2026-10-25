import Mathlib
import Structure.ModularCurve_MazurPrincipleCore
import Def.ModularCurve_DeligneRapoport
import Lemma.ModularCurve.HeckeOperator
import Structure.Isogeny_ConditionalCurrency

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generic

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

structure IsAbelianPartDataQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (δ : Fin 2 → J →+ J₀) : Prop where

  toric_le_ker : ∀ i : Fin 2, ∀ x ∈ 𝒯, δ i x = 0

  goodPrime_equivariant : ∀ i : Fin 2, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    ∀ x : J, δ i (heckeGen ℓ • x) = heckeGen ℓ • δ i x

  component_eisenstein : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → (∀ i : Fin 2, δ i x = 0) → x ∈ 𝒯


namespace ExistsToricData

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}


end ExistsToricData


namespace ExistsToricDataQGuarded

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}


end ExistsToricDataQGuarded


namespace ExistsToricDataFullQGuarded

variable {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {δ : Fin 2 → J →+ J₀}


end ExistsToricDataFullQGuarded

end Generic

section Degeneracy

variable (N q : ℕ) [NeZero N] [NeZero q]


open Classical in


variable {N q}


end Degeneracy

end ModularCurve

end
