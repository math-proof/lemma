import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_ModularCurve_DeligneRapoport
import Lemma.Definitions.Def_ModularCurve_EigenformIdeal
import Lemma.Definitions.Def_ModularCurve_MultiplicativeType

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section FiltrationPredicates

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def IsAtPFiltration (I : Subgroup G) (χ : G →* Rˣ) (W : Submodule R J) : Prop :=
  W ≠ ⊤ ∧ ToricStable G W ∧ MultiplicativeType I χ W ∧ InertiaUnipotentTowards I W

end FiltrationPredicates

section EisensteinComponentGroup

variable (S : Finset Nat.Primes) (Φ : Type*) [AddCommGroup Φ] [Module HeckeAlg Φ]

def EisensteinAnnihilates : Prop :=
  ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ x : Φ,
    (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0

end EisensteinComponentGroup

section SupportDescends

variable (N₀ : ℕ) [NeZero N₀]

def AtPSupportDescends (S : Finset Nat.Primes) (fin : Ideal HeckeAlg → Prop)
    (Wet : Type*) [AddCommGroup Wet] [Module HeckeAlg Wet] : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal →
    (∃ ℓ : Nat.Primes, ℓ ∉ S ∧ heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) →
    fin 𝔪 →
    heckeTorsion Wet 𝔪 ≠ ⊥ →
    IsEigenformIdeal N₀ 𝔪

end SupportDescends

end ModularCurve

end
