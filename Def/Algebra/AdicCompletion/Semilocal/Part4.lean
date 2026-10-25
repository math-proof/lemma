import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal.Part4
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

noncomputable def ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) :
    AdicCompletion I S :=
  ⟨fun n => Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n), by
    intro m n hmn
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
    have hzm : z m = Ideal.Quotient.mk (I ^ m) r := by
      rw [← hz hmn, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    show transitionMap I S hmn (Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n)) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I m).symm (z m)
    rw [← hr, hzm, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
    rfl⟩

end AdicCompletion
end Assembly
