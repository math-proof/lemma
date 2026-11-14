import Def.GaloisRep_LocalConditions
import Def.GaloisRep_StrictOrdinary

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]


theorem IsStrictOrdinaryAt.isOrdinaryAt {ρ : GaloisRepAdic A} {p : ℕ}
    (h : ρ.IsStrictOrdinaryAt p) : ρ.IsOrdinaryAt p := fun P hP => by
  obtain ⟨L, hb, hD, hI, -⟩ := h.2 P hP
  exact ⟨L, hb, hD, hI⟩

end GaloisRepAdic

namespace GaloisRep


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
