import Def.HeckeGalois_EichlerShimura

set_option autoImplicit false

open MvPolynomial

namespace ModularCurve

def IsEventuallyEisenstein (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ S : Finset Nat.Primes, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪


def HasLowerLevelTorsion (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) (J₀ : Type*)
    [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∃ y : J₀, y ≠ 0 ∧
    (∀ n : ℕ, (n : HeckeAlg) ∈ 𝔪 → (n : HeckeAlg) • y = 0) ∧
    ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ b : ℤ, heckeGen ℓ - C b ∈ 𝔪 →
      (heckeGen ℓ - C b) • y = 0

end ModularCurve
