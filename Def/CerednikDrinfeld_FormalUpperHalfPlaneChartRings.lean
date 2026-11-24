module
public import Mathlib
public import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
public import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings
public import Abbrev.CerednikDrinfeld_FormalUpperHalfPlaneChartRings
set_option autoImplicit false


public section

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]

namespace chartVRing

variable (q : ℕ)

def ζ : chartVRing R q := algebraMap R[X] (chartVRing R q) X

def point : (chartV R q).obj (chartVRing R q) := ⟨ζ R q, isUnit_ζ_pow_sub R q⟩

variable {R q}

def lift {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B) : chartVRing R q →ₐ[R] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (vertexDiscr R q)) (f := Polynomial.aeval (R := R) x.1)
    (isUnit_aeval_of_mem_powers x)

variable (R q) in

def corepEquiv (B : Type) [CommRing B] [Algebra R B] :
    (chartVRing R q →ₐ[R] B) ≃ (chartV R q).obj B where
  toFun φ := (chartV R q).map φ (point R q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (vertexDiscr R q))
    apply Polynomial.algHom_ext
    show lift ((chartV R q).map φ (point R q)) (algebraMap R[X] _ X) = φ (algebraMap R[X] _ X)
    exact lift_ζ _
  right_inv x := Subtype.ext (lift_ζ x)

variable (R q) in

def corepNatTrans : AlgFunctor.NatTrans (AlgFunctor.corep (𝒪 := R) (chartVRing R q)) (chartV R q) where
  app B _ _ φ := corepEquiv R q B φ
  naturality f φ := corepEquiv_natural f φ

end chartVRing

def edgeQuot (π : R) : Type := MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}

def edgeQuot.mk (π : R) : MvPolynomial (Fin 2) R →ₐ[R] edgeQuot R π :=
  Ideal.Quotient.mkₐ R (Ideal.span {edgeRel R π})

def edgeQuot.discr (π : R) (q : ℕ) : edgeQuot R π := edgeQuot.mk R π (edgeDiscr R q)

abbrev chartERing (π : R) (q : ℕ) : Type := Localization.Away (edgeQuot.discr R π q)

namespace chartERing

variable (π : R) (q : ℕ)

def ofPoly : MvPolynomial (Fin 2) R →ₐ[R] chartERing R π q :=
  (Algebra.algHom R (edgeQuot R π) (chartERing R π q)).comp (edgeQuot.mk R π)

def ξ : chartERing R π q := ofPoly R π q (MvPolynomial.X 0)

def η : chartERing R π q := ofPoly R π q (MvPolynomial.X 1)

def point : (chartE R π q).obj (chartERing R π q) :=
  ⟨(ξ R π q, η R π q), ξ_mul_η R π q, isUnit_of_mul_isUnit_left (isUnit_discr R π q),
    isUnit_of_mul_isUnit_right (isUnit_discr R π q)⟩

variable {R π q}

abbrev evalPoly {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : MvPolynomial (Fin 2) R →ₐ[R] B :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then x.1.1 else x.1.2)

def evalQuot {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : edgeQuot R π →ₐ[R] B :=
  Ideal.Quotient.liftₐ (Ideal.span {edgeRel R π}) (evalPoly x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul (evalPoly x), evalPoly_edgeRel, mul_zero])

def lift {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : chartERing R π q →ₐ[R] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (edgeQuot.discr R π q))
    (f := evalQuot x) (isUnit_evalQuot_of_mem_powers x)

variable (R π q) in

def corepEquiv (B : Type) [CommRing B] [Algebra R B] :
    (chartERing R π q →ₐ[R] B) ≃ (chartE R π q).obj B where
  toFun φ := (chartE R π q).map φ (point R π q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (edgeQuot.discr R π q))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show lift ((chartE R π q).map φ (point R π q)) (ofPoly R π q (MvPolynomial.X i)) = φ (ofPoly R π q (MvPolynomial.X i))
    fin_cases i
    · exact lift_ξ _
    · exact lift_η _
  right_inv x := Subtype.ext (Prod.ext (lift_ξ x) (lift_η x))

variable (R π q) in

def corepNatTrans : AlgFunctor.NatTrans (AlgFunctor.corep (𝒪 := R) (chartERing R π q)) (chartE R π q) where
  app B _ _ φ := corepEquiv R π q B φ
  naturality f φ := corepEquiv_natural f φ

end chartERing

section Level

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q n : ℕ)

abbrev chartERingMod : Type :=
  chartERing (truncRing 𝒪 π n) (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) π) q

end Level

end ChartRings

end FormalOmega
end CerednikDrinfeld

end
