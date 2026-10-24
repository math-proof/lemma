import Lemma.Definitions.Def_GaloisRep_LocalConditions

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def IsStrictOrdinaryAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  (p : A) ∈ IsLocalRing.maximalIdeal A ∧
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∃ x z : A,
        (∀ w ∈ L, ρ.ρ σ w = x • w) ∧ (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧
        ∀ (n a : ℕ), (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
          x - (a : A) * z ∈ Ideal.span {((p ^ n : ℕ) : A)})

theorem IsStrictOrdinaryAt.isOrdinaryAt {ρ : GaloisRepAdic A} {p : ℕ}
    (h : ρ.IsStrictOrdinaryAt p) : ρ.IsOrdinaryAt p := fun P hP => by
  obtain ⟨L, hb, hD, hI, -⟩ := h.2 P hP
  exact ⟨L, hb, hD, hI⟩

end GaloisRepAdic

namespace GaloisRep

def strictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsStrictOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalStrictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => strictOrdinaryCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

theorem ordinaryCondition_of_strictOrdinaryCondition {𝒪 : Type} [CommRing 𝒪] {p : ℕ}
    {S : Finset ℕ} {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] {ρ : GaloisRepAdic A}
    (h : strictOrdinaryCondition 𝒪 p S ρ) : ordinaryCondition 𝒪 p S ρ :=
  ⟨h.1, h.2.1.isOrdinaryAt, h.2.2⟩

theorem minimalOrdinaryCondition_of_minimalStrictOrdinaryCondition {𝒪 : Type} [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    {ρ : GaloisRepAdic A} (h : minimalStrictOrdinaryCondition 𝒪 p S ρ) :
    minimalOrdinaryCondition 𝒪 p S ρ :=
  ⟨ordinaryCondition_of_strictOrdinaryCondition h.1, h.2⟩

end GaloisRep
