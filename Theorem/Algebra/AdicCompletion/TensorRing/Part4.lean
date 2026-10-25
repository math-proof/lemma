import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part3
import Def.Algebra.AdicCompletion.TensorRing.Part4
universe u₁ u₂

open scoped TensorProduct


section SameUniverse

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₁) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

@[simp]
theorem tensorRingEquiv_tmul [IsNoetherianRing A] [Module.Finite A B]
    (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingEquiv B 𝔭 (x ⊗ₜ[A] b) =
      completionBaseChangeHom B 𝔭 x * of (𝔭.map (algebraMap A B)) B b :=
  tensorRingHom_tmul B 𝔭 x b

end AdicCompletion
end SameUniverse
