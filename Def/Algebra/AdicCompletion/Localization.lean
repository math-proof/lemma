import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.Semilocal.Part6
import Theorem.Algebra.AdicCompletion.TensorRing.Part4
import Theorem.Algebra.AdicCompletion.GaloisAction.Part6
import Theorem.Algebra.AdicCompletion.Localization
open IsLocalRing

open scoped AdicCompletion.GaloisAction


namespace BDescN6

/-- Localization-at-prime induces an equivalence of adic completions. -/
noncomputable def adicEquiv {C : Type*} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    AdicCompletion 𝔫 C ≃+* AdicCompletion (maximalIdeal S) S :=
  (AdicCompletion.mapAlgEquivOfBijective 𝔫 (maximalIdeal S) (Algebra.ofId C S)
    (map_le 𝔫 S) (levelMap_bijective 𝔫 S)).toRingEquiv

end BDescN6
