import Mathlib
import Lemma.Definitions.Def_GaloisRep_Adic
import Lemma.Definitions.Def_Deformations_TraceAlgebra

namespace GaloisRep

open Deformation CategoryTheory IsLocalRing

def conditionLifts (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField)
    (A : ProartinianCat 𝒪) :
    Set ((repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj A) :=
  {ρ' | ρ' ∈ (liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).obj A ∧
    ∀ (B : ProartinianCat 𝒪) [IsArtinianRing B] (f : A ⟶ B) (ρB : GaloisRepAdic B)
      (b : Module.Basis (Fin 2) B ρB.V),
      (∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) =
        ((mapRepn (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 f ρ' σ : GL (Fin 2) B) :
          Matrix (Fin 2) (Fin 2) B)) → 𝒟 ρB}

def conditionSubfunctor (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField) :
    Subfunctor (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪) where
  obj A := conditionLifts 𝒪 𝒟 ρ₀ A
  map {A A'} g := by
    rintro ρ' ⟨hlift, hD⟩
    refine ⟨(liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).map g hlift, ?_⟩
    intro B _ f ρB b hb
    refine hD B (g ≫ f) ρB b (fun σ => ?_)
    rw [hb σ]
    simp only [mapRepn, Functor.map_comp, types_comp_apply]

@[simp] lemma conditionSubfunctor_obj (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField) (A : ProartinianCat 𝒪) :
    (conditionSubfunctor 𝒪 𝒟 ρ₀).obj A = conditionLifts 𝒪 𝒟 ρ₀ A := rfl

end GaloisRep
