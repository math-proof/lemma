import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.Semilocal.Part2
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem semilocalComponent_of {P : Ideal S} (hIP : I ≤ P) (x : S) :
    semilocalComponent I hIP (of I S x) = of P S x := by
  simp [semilocalComponent]

end AdicCompletion
end Assembly
