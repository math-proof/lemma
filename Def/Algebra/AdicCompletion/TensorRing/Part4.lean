import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Theorem.Algebra.AdicCompletion.TensorRing.Part3
universe u₁ u₂

open scoped TensorProduct


section SameUniverse

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₁) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def tensorRingEquiv [IsNoetherianRing A] [Module.Finite A B] :
    (AdicCompletion 𝔭 A ⊗[A] B) ≃ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  AlgEquiv.ofBijective (tensorRingHom B 𝔭) (tensorRingHom_bijective B 𝔭)

end AdicCompletion
end SameUniverse
