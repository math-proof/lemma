import Structure.HeckeGalois_EichlerShimura
import Def.ModularCurve_MazurPrincipleCore

set_option autoImplicit false

open MvPolynomial

namespace ModularCurve


section AbelianPart

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  [SMulCommClass G HeckeAlg J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

structure IsAbelianPartData (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (δ : Fin 2 → J →+ J₀) : Prop where

  toric_le_ker : ∀ i : Fin 2, ∀ x ∈ 𝒯, δ i x = 0

  goodPrime_equivariant : ∀ i : Fin 2, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    ∀ x : J, δ i (heckeGen ℓ • x) = heckeGen ℓ • δ i x

  component_eisenstein : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → (∀ i : Fin 2, δ i x = 0) → x ∈ 𝒯

namespace IsAbelianPartData

variable {S : Finset Nat.Primes} {I : Subgroup G} {𝒯 : Submodule HeckeAlg J}
  {δ : Fin 2 → J →+ J₀}


end IsAbelianPartData


end AbelianPart

end ModularCurve
