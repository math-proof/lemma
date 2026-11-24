module
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
public import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
public import Theorem.Algebra.AdicCompletion.TensorRing


public section

universe u₁ u₂

open scoped TensorProduct


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def completionOfAlgHom :
    B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  IsScalarTower.toAlgHom A B _

end AdicCompletion
