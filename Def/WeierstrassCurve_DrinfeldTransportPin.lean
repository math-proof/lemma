import Mathlib
import Lemma.WeierstrassCurve.ProjModel
import Def.WeierstrassCurve_DrinfeldBasisGlobal
import Abbrev.WeierstrassCurve_DrinfeldTransportPin

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

def IsVariableChangeHom {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
    (C : WeierstrassCurve.VariableChange T) (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W)) : Prop :=
  (∀ a : T, φ (cls W (MvPolynomial.C a)) = cls (C • W) (MvPolynomial.C a)) ∧
  φ (cls W (X 0)) = cls (C • W) (MvPolynomial.C ((C.u : T) ^ 2) * X 0 + MvPolynomial.C C.r * X 2) ∧
  φ (cls W (X 1)) = cls (C • W)
    (MvPolynomial.C ((C.u : T) ^ 3) * X 1 + MvPolynomial.C ((C.u : T) ^ 2 * C.s) * X 0 + MvPolynomial.C C.t * X 2) ∧
  φ (cls W (X 2)) = cls (C • W) (X 2)

def IsCoefficientHom {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f)) : Prop :=
  (∀ a : T, φ (cls W (MvPolynomial.C a)) = cls (W.map f) (MvPolynomial.C (f a))) ∧
  ∀ i : Fin 3, φ (cls W (X i)) = cls (W.map f) (X i)

variable {A : Type u} [CommRing A]

def DrinfeldTransport.IsSectionTransport {𝒢 : GroupLawFamily A} {q : ℕ} (𝒯 : DrinfeldTransport A 𝒢 q) : Prop :=
  (∀ (T : Type u) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.act C x).curve = C • x.curve,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (C • x.curve))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • x.curve)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsVariableChangeHom x.curve C φ →
          (𝒯.act C x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.P.1 ∧
          (𝒯.act C x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.Q.1) ∧
  (∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.map f x).curve = x.curve.map f.toRingHom,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsCoefficientHom x.curve f.toRingHom φ →
          (𝒯.map f x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1 ∧
          (𝒯.map f x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1)

end WeierstrassCurve.DrinfeldGlobal

end
