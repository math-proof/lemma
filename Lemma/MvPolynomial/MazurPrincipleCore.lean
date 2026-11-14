import Def.HeckeGalois_EichlerShimura
import Def.ModularCurve_MazurPrincipleCore
import Structure.ModularCurve_MazurPrincipleCore

set_option autoImplicit false

open MvPolynomial

namespace ModularCurve


section AbelianPart

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  [SMulCommClass G HeckeAlg J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]


namespace IsAbelianPartData

variable {S : Finset Nat.Primes} {I : Subgroup G} {𝒯 : Submodule HeckeAlg J}
  {δ : Fin 2 → J →+ J₀}

theorem mem_toric_or_exists_ne_zero (h : IsAbelianPartData S I 𝒯 δ)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) (heis : ¬ IsEventuallyEisenstein 𝔪)
    {x : J} (hx : x ∈ heckeTorsion J 𝔪) (hinv : ∀ σ ∈ I, σ • x = x) :
    x ∈ 𝒯 ∨ ∃ i : Fin 2, δ i x ≠ 0 := by
  by_cases hker : ∀ i : Fin 2, δ i x = 0
  · exact Or.inl (h.component_eisenstein 𝔪 hmax heis x hx hinv hker)
  · exact Or.inr (not_forall.mp hker)

theorem heckeGen_sub_smul_image_eq_zero (h : IsAbelianPartData S I 𝒯 δ) (i : Fin 2)
    {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) (b : ℤ) {x : J}
    (hx : (heckeGen ℓ - C b) • x = 0) :
    (heckeGen ℓ - C b) • δ i x = 0 := by
  rw [sub_smul] at hx ⊢
  rw [eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg) b] at hx ⊢
  rw [← h.goodPrime_equivariant i ℓ hℓ x,
    ← map_intCast_smul (δ i) HeckeAlg HeckeAlg b x, ← map_sub, hx, map_zero]

end IsAbelianPartData

theorem natCast_smul_addMonoidHom_eq_zero (f : J →+ J₀) (n : ℕ)
    {x : J} (hx : (n : HeckeAlg) • x = 0) : (n : HeckeAlg) • f x = 0 := by
  rw [← map_natCast_smul f HeckeAlg HeckeAlg n x, hx, map_zero]

end AbelianPart

end ModularCurve
