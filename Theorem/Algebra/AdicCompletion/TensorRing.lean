import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Def.Algebra.AdicCompletion.TensorRing
universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

@[simp]
theorem completionBaseChangeHom_of (x : A) :
    completionBaseChangeHom B 𝔭 (of 𝔭 A x) =
      of (𝔭.map (algebraMap A B)) B (algebraMap A B x) := by
  simp [completionBaseChangeHom, Algebra.ofId_apply]

end AdicCompletion
