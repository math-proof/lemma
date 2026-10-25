import Instance.AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra
import Def.AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassProjModel


end WeierstrassProjModel

namespace WeierstrassProjModel

open NeronModelInfra

def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩

@[simp]

structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) where

  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f

  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f

  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f

  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)

  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x

  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x

  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t

  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


end RelativeGroupLaw

end WeierstrassProjModel
end

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


end RelativeGroupLaw

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open NeronModelInfra

namespace WeierstrassProjModel


section Carrier

variable {R : Type*} [CommRing R]


end Carrier

section PointsEval

variable {R : Type u} [CommRing R]


end PointsEval

end WeierstrassProjModel

end
