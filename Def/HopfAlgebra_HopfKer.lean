import Mathlib

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]

noncomputable def coaction (π : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)).comp (Bialgebra.comulAlgHom R A)


noncomputable def hopfKer (π : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (coaction π) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)


noncomputable def canAlgHom (π : A →ₐc[R] B) : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (coaction π)
    (fun _ _ => Commute.all _ _)


noncomputable def canMap (π : A →ₐc[R] B) : A ⊗[R] A →ₗ[R] A ⊗[R] B := (canAlgHom π).toLinearMap


def balancingRelations (π : A →ₐc[R] B) : Set (A ⊗[R] A) :=
  {x | ∃ (a h a' : A), h ∈ hopfKer π ∧ x = (a * h) ⊗ₜ[R] a' - a ⊗ₜ[R] (h * a')}


def IsHopfGalois (π : A →ₐc[R] B) : Prop :=
  Function.Surjective (canMap π) ∧ ∀ z, canMap π z = 0 → z ∈ Submodule.span R (balancingRelations π)

end HopfAlgebra
