import Mathlib
import Lemma.AlgebraicGeometry.ProjSpaceCover
import Instance.AlgebraicGeometry_ProjSpaceCechGradedModule
import Instance.AlgebraicGeometry_ProjTwistDatum

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace


variable (A : Type u) [CommRing A] (N : ℕ)

local notation "S" => MvPolynomial (Fin (N + 1)) A


end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry


namespace ProjSpace

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def pullbackChart (i : Fin (N + 1)) : X.Opens :=
  φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i)


def frameUnit (i j : Fin (N + 1)) : Γ(X, pullbackChart φ i) :=
  (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i))).hom
    ((Proj.awayToSection _ (MvPolynomial.X i)).hom (ProjSpace.ratio A N i j))

abbrev restrictFun {U U' : X.Opens} (h : U ≤ U') : Γ(X, U') →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

def TwistCompat (m : ℕ) (U : X.Opens) (g : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) : Prop :=
  ∀ i j : Fin (N + 1),
    restrictFun (inf_le_left : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ i) (g i)
      = restrictFun (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i) (frameUnit φ i j) ^ m
        * restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ j) (g j)


end ProjSpace

end AlgebraicGeometry

namespace AlgebraicGeometry
namespace ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}


@[ext] structure twistObj (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Type u where

  val : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)

  compat : TwistCompat φ m U val


end ProjSpace
end AlgebraicGeometry

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}


end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

section GradedModuleOfTwist

variable (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


end GradedModuleOfTwist

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


end AlgebraicGeometry.ProjSpace

end
