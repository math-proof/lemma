import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.Semilocal
universe u₁ u₂


namespace Ideal

variable {S : Type u₁} [CommRing S]

variable (I : Ideal S)

theorem quotientPowEquivPiSup_mk [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (x : S) :
    quotientPowEquivPiSup I hc (Ideal.Quotient.mk _ x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.mk (I ^ n ⊔ (P : Ideal S) ^ c) x := by
  funext _P
  simp [quotientPowEquivPiSup, Ideal.quotientInfRingEquivPiQuotient,
    Ideal.quotientInfToPiQuotient]

end Ideal

section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem map_algHom_id_le {P : Ideal S} (hIP : I ≤ P) :
    I.map (AlgHom.id S S) ≤ P := by
  simp [hIP]

end AdicCompletion
end Assembly
