import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.Semilocal.Part3
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem semilocalPiHom_apply (x : AdicCompletion I S)
    (P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}) :
    semilocalPiHom I x P = semilocalComponent I P.2.2 x := rfl

theorem semilocalPiHom_of (x : S) :
    semilocalPiHom I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x := by
  funext P
  exact semilocalComponent_of I P.2.2 x

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal S) = I ^ n := by
  ext x; simp

end AdicCompletion
end Assembly
