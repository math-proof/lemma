import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Def.Algebra.AdicCompletion.TensorRing.Part2
universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

@[simp]
theorem completionOfAlgHom_apply (b : B) :
    completionOfAlgHom B 𝔭 b = of (𝔭.map (algebraMap A B)) B b := rfl

end AdicCompletion
