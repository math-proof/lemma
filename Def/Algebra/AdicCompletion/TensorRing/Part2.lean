import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Theorem.Algebra.AdicCompletion.TensorRing
universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def completionOfAlgHom :
    B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  IsScalarTower.toAlgHom A B _

end AdicCompletion
