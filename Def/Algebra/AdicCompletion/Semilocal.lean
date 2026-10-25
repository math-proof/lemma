import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal
universe u₁ u₂


namespace Ideal

variable {S : Type u₁} [CommRing S]

variable (I : Ideal S)

noncomputable def quotientPowEquivPiSup [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) :
    (S ⧸ I ^ n) ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, S ⧸ (I ^ n ⊔ (P : Ideal S) ^ c) :=
  have := finite_setOf_isMaximal_and_le I
  (Ideal.quotEquivOfEq (iInf_sup_pow_eq I hc).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hPQ => isCoprime_sup_pow_of_ne I hPQ)

end Ideal
