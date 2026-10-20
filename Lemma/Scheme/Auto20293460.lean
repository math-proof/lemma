import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat
  (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Module.Flat A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
  IsReduced B := by
  let K := FractionRing A
  let _ : IsReduced (K ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[A] B)
  let φ : B →ₐ[A] K ⊗[A] B := Algebra.TensorProduct.includeRight
  refine isReduced_of_injective φ ?_
  have h1 : Function.Injective ((Algebra.linearMap A K).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
  have hφ' : ⇑φ = ((Algebra.linearMap A K).rTensor B) ∘ (TensorProduct.lid A B).symm := by
    ext b
    simp [φ, Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
  rw [hφ']
  apply h1.comp
  apply (TensorProduct.lid A B).symm.injective

/--
[AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) [Flat f] [FormallyUnramified f] [LocallyOfFiniteType f] [IsIntegral Y] :
  -- imply
  IsReduced X := by
  -- proof
  let _ : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    let _ := (f.stalkMap x).hom.toAlgebra
    let _ : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    let _ : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      FormallyUnramified.stalkMap f x
    let _ : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      LocallyOfFiniteType.stalkMap f x
    apply Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
  apply isReduced_of_isReduced_stalk X


-- created on 2026-10-20
