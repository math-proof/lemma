import Mathlib
import Def.GaloisRep_Adic
import Lemma.Deformations.TraceAlgebra
import Def.GaloisRep_ConditionLifts

namespace GaloisRep

open Deformation CategoryTheory IsLocalRing


@[simp] lemma conditionSubfunctor_obj (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField) (A : ProartinianCat 𝒪) :
    (conditionSubfunctor 𝒪 𝒟 ρ₀).obj A = conditionLifts 𝒪 𝒟 ρ₀ A := rfl

end GaloisRep
