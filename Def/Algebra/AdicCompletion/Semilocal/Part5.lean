import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal.Part5
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
