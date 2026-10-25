import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Theorem.Algebra.AdicCompletion.TensorRing.Part2
universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def tensorRingHom :
    (AdicCompletion 𝔭 A) ⊗[A] B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  Algebra.TensorProduct.productMap (completionBaseChangeHom B 𝔭) (completionOfAlgHom B 𝔭)

end AdicCompletion
