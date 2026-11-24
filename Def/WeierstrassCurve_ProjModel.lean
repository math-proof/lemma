module
public import Def.Ideal_HomogeneousIdealQuotientGradingInfra
public import Theorem.WeierstrassCurve.ProjectiveWeierstrassPolynomialPrime
public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Structure.WeierstrassCurve_ProjModel
public import Abbrev.WeierstrassCurve_ProjModel
set_option autoImplicit false


public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Ideal Scheme WeierstrassCurve


namespace WeierstrassProjModel

open NeronModelInfra

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[reducible]
def pointGroup (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

end RelativeGroupLaw

end WeierstrassProjModel
end

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra Ideal Scheme WeierstrassCurve

namespace WeierstrassProjModel

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial Ideal Scheme WeierstrassCurve
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open NeronModelInfra

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

section Carrier

variable {R : Type*} [CommRing R]

def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩

abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ :=
  MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal

abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) :
    ℕ → Submodule R (ProjModelRingCR V) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal

abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme :=
  Proj (projModelGradingCR V)

def projModelStrCR (V : WeierstrassCurve.Projective R) :
    Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))

end Carrier

section PointsEval

variable {R : Type u} [CommRing R]

def galTwist {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {F : Type u} [Field F]
    [Algebra R F] (σ : F ≃ₐ[R] F)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f :=
  schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : F →+* F)))
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom
        (RingHom.ext fun x => σ.commutes x)))
    P

def IsPointsEval (V : WeierstrassCurve.Projective R)
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point) : Prop :=
  (∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F]
      (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F)))
        (projModelStrCR V)),
      ev F (G.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q) = ev F P + ev F Q) ∧
  (∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (σ : F ≃ₐ[R] F)
      (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F)))
        (projModelStrCR V)),
      ev F (galTwist σ P) =
        WeierstrassCurve.Affine.Point.map (σ : F →ₐ[R] F) (ev F P))

end PointsEval

end WeierstrassProjModel

end
