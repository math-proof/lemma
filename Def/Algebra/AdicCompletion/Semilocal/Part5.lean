module
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
public import Theorem.Algebra.AdicCompletion.Semilocal.Part5


public section

universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ I)]

omit [IsArtinianRing (S ⧸ I)] in

noncomputable def semilocalPiEquiv :
    AdicCompletion I S ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingEquiv.ofBijective (semilocalPiHom I)
    ⟨semilocalPiHom_injective I, semilocalPiHom_surjective I⟩

end AdicCompletion
end Assembly
