import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal.Part2
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

noncomputable def semilocalComponent {P : Ideal S} (hIP : I ≤ P) :
    AdicCompletion I S →ₐ[S] AdicCompletion P S :=
  mapₐ I P (AlgHom.id S S) (map_algHom_id_le I hIP)

end AdicCompletion
end Assembly
