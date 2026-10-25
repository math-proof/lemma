import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def completionBaseChangeHom :
    AdicCompletion 𝔭 A →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  mapₐ 𝔭 (𝔭.map (algebraMap A B)) (Algebra.ofId A B)
    (le_of_eq (rfl : 𝔭.map (Algebra.ofId A B) = 𝔭.map (algebraMap A B)))

end AdicCompletion
