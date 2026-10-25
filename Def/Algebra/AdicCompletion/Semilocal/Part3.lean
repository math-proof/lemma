import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal.Part3
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

noncomputable def semilocalPiHom :
    AdicCompletion I S →+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingHom.pi fun P => (semilocalComponent I P.2.2).toRingHom

end AdicCompletion
end Assembly
