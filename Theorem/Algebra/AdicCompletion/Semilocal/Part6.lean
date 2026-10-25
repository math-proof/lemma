import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.Semilocal.Part5
universe u₁ u₂


section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ I)]

theorem semilocalPiEquiv_of (x : S) :
    semilocalPiEquiv I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x :=
  semilocalPiHom_of I x

theorem semilocalPiEquiv_apply {𝔫 : Ideal S} [h𝔫 : 𝔫.IsMaximal] (hI : I ≤ 𝔫)
    (y : AdicCompletion I S) :
    semilocalPiEquiv I y ⟨𝔫, h𝔫, hI⟩ = semilocalComponent I hI y :=
  semilocalPiHom_apply I y ⟨𝔫, h𝔫, hI⟩

end AdicCompletion
end Assembly
