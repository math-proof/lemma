import Mathlib
import Lemma.ModularCurve.ToricDescentData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Dichotomy

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]

def IsToricDichotomyQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (J₀ : Type*) [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → x ∈ 𝒯 ∨ HasLowerLevelTorsion S 𝔪 J₀

end Dichotomy

section Bundle

def ExistsToricDichotomyDataQGuarded {G : Type*} [Group G]
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    (q : Nat.Primes) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (J₀ : Type*) [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J,
    ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧ IsToricDichotomyQGuarded (q : ℕ) S I 𝒯 J₀ ∧
    ToricFrobeniusHecke q φ 𝒯

namespace ExistsToricDichotomyDataQGuarded

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

def toric (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) : Submodule HeckeAlg J :=
  h.choose

end ExistsToricDichotomyDataQGuarded

end Bundle

end ModularCurve

end
