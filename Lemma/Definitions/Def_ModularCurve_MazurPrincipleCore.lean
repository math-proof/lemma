import Lemma.Definitions.Def_HeckeGalois_EichlerShimura

set_option autoImplicit false

open MvPolynomial

namespace ModularCurve

def IsEventuallyEisenstein (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ S : Finset Nat.Primes, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪

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

def HasLowerLevelTorsion (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) (J₀ : Type*)
    [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∃ y : J₀, y ≠ 0 ∧
    (∀ n : ℕ, (n : HeckeAlg) ∈ 𝔪 → (n : HeckeAlg) • y = 0) ∧
    ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ b : ℤ, heckeGen ℓ - C b ∈ 𝔪 →
      (heckeGen ℓ - C b) • y = 0

end ModularCurve
