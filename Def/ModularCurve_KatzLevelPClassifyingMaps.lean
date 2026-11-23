import Mathlib
import Def.ModularCurve_KatzLevelP
import Def.ModularCurve_KatzLevelPUniversal
import Instance.ModularCurve_KatzLevelPClassifyingMaps
import Abbrev.ModularCurve_KatzLevelPClassifyingMaps

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section TorsionPointLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (x y : T)

def PsiRoot.lift (hx : ((W.map φ).preΨ p).eval x = 0) : PsiRoot W p →+* T :=
  AdjoinRoot.lift φ x (eval₂_preΨ_eq_zero W p φ x hx)

def TorsionPointRing.lift (hx : ((W.map φ).preΨ p).eval x = 0)
    (hy : (W.map φ).toAffine.Equation x y) : TorsionPointRing W p →+* T :=
  AdjoinRoot.lift (PsiRoot.lift W p φ x hx) y (torsionQuadratic_eval₂_eq_zero W p φ x y hx hy)

variable (hx : ((W.map φ).preΨ p).eval x = 0) (hy : (W.map φ).toAffine.Equation x y)

end TorsionPointLift

section BasisRingLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (D : LevelPData T) (hD : IsLevelPStructure (W.map φ) p D)

def onePointLift : TorsionPointRing W p →+* T :=
  TorsionPointRing.lift W p φ D.xP D.yP hD.preΨ_P hD.equation_P

def twoPointLift : TwoPointRing W p →+* T :=
  TorsionPointRing.lift (torsionPtCurve W p) p (onePointLift W p φ D hD) D.xQ D.yQ
    (by rw [torsionPtCurve_map_onePointLift]; exact hD.preΨ_Q)
    (by rw [torsionPtCurve_map_onePointLift]; exact hD.equation_Q)

def BasisRing.lift : BasisRing W p →+* T :=
  IsLocalization.Away.lift (indepDenom W p) (isUnit_twoPointLift_indepDenom W p φ D hD)

end BasisRingLift

section Univ

variable (p : ℕ) {T : Type v} [CommRing T]

def genericLift (W : WeierstrassCurve T) : MvPolynomial (Fin 5) ℤ →+* T :=
  MvPolynomial.eval₂Hom (Int.castRingHom T) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

def UnivBase.lift (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ)) : UnivBase p →+* T :=
  IsLocalization.Away.lift (pDelta p) (isUnit_genericLift_pDelta p W hW)

variable (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ))

variable (D : LevelPData T) (hD : IsLevelPStructure W p D)

include hD in
def UnivBasisRing.classify (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ)) (D : LevelPData T)
    (hD : IsLevelPStructure W p D) : UnivBasisRing p →+* T :=
  BasisRing.lift (univCurve p) p (UnivBase.lift p W hW) D (isLevelPStructure_map_univBaseLift p W hW D hD)

end Univ

section VC

variable (p : ℕ)

def VCRing : Type := Localization.Away (MvPolynomial.X 0 : VCPoly p)

def VCRing.ofUniv : UnivBasisRing p →+* VCRing p := algebraMap (UnivBasisRing p) (VCRing p)

def vcVar (i : Fin 4) : VCRing p := algebraMap (VCPoly p) (VCRing p) (MvPolynomial.X i)

def univVC : VariableChange (VCRing p) :=
  ⟨(isUnit_vcVar_zero p).unit, vcVar p 1, vcVar p 2, vcVar p 3⟩

def vcCurve : WeierstrassCurve (VCRing p) := (univCurveT p).map (VCRing.ofUniv p)

def vcData : LevelPData (VCRing p) := (univData p).map (VCRing.ofUniv p)

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (C : VariableChange T)

def vcPolyLift : VCPoly p →+* T := MvPolynomial.eval₂Hom φ ![(C.u : T), C.r, C.s, C.t]

def VCRing.lift : VCRing p →+* T :=
  IsLocalization.Away.lift (MvPolynomial.X 0 : VCPoly p) (g := vcPolyLift p φ C)
    (by rw [vcPolyLift_X]; exact Units.isUnit C.u)

end VC

section Borel

variable (p : ℕ) (a : ℕ)

def borelX : UnivBasisRing p :=
  ((univCurveT p).Φ a).eval (univData p).xQ * Ring.inverse (((univCurveT p).ΨSq a).eval (univData p).xQ)

def borelQuadratic : Polynomial (UnivBasisRing p) :=
  X ^ 2 + C ((univCurveT p).a₁ * borelX p a + (univCurveT p).a₃) * X -
    C (borelX p a ^ 3 + (univCurveT p).a₂ * borelX p a ^ 2 + (univCurveT p).a₄ * borelX p a +
      (univCurveT p).a₆)

abbrev BorelQRing : Type := AdjoinRoot (borelQuadratic p a)

def borelQY : BorelQRing p a := AdjoinRoot.root (borelQuadratic p a)

def borelQCurve : WeierstrassCurve (BorelQRing p a) := (univCurveT p).map (AdjoinRoot.of (borelQuadratic p a))

abbrev BorelPRing : Type := TorsionPointRing (borelQCurve p a) p

def BorelPRing.ofUniv : UnivBasisRing p →+* BorelPRing p a :=
  (TorsionPointRing.ofBase (borelQCurve p a) p).comp (AdjoinRoot.of (borelQuadratic p a))

def BorelPRing.xP : BorelPRing p a := torsionPtX (borelQCurve p a) p

def BorelPRing.yP : BorelPRing p a := torsionPtY (borelQCurve p a) p

def BorelPRing.xQ : BorelPRing p a := BorelPRing.ofUniv p a (borelX p a)

def BorelPRing.yQ : BorelPRing p a := TorsionPointRing.ofBase (borelQCurve p a) p (borelQY p a)

abbrev borelPCurve : WeierstrassCurve (BorelPRing p a) := torsionPtCurve (borelQCurve p a) p

def borelDenom : BorelPRing p a :=
  indepElt (borelPCurve p a) p (BorelPRing.xP p a) (BorelPRing.xQ p a) *
    indepElt (borelPCurve p a) p (BorelPRing.xQ p a) (BorelPRing.xP p a)

def BorelRing : Type := Localization.Away (borelDenom p a)

def BorelRing.ofUniv : UnivBasisRing p →+* BorelRing p a := algebraMap (UnivBasisRing p) (BorelRing p a)

def borelCurve : WeierstrassCurve (BorelRing p a) := (univCurveT p).map (BorelRing.ofUniv p a)

def borelData : LevelPData (BorelRing p a) := (univData p).map (BorelRing.ofUniv p a)

def borelData' : LevelPData (BorelRing p a) :=
  ⟨algebraMap _ _ (BorelPRing.xP p a), algebraMap _ _ (BorelPRing.yP p a),
    algebraMap _ _ (BorelPRing.xQ p a), algebraMap _ _ (BorelPRing.yQ p a)⟩

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
  (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a))

include hD' hxQ in
def BorelQRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelQRing p a →+* T :=
  AdjoinRoot.lift φ D'.yQ (borelQuadratic_eval₂_eq_zero p a φ D' hD' hxQ)

def BorelPRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelPRing p a →+* T :=
  TorsionPointRing.lift (borelQCurve p a) p (BorelQRing.lift p a φ D' hD' hxQ) D'.xP D'.yP
    (by rw [borelQCurve_map_lift]; exact hD'.preΨ_P) (by rw [borelQCurve_map_lift]; exact hD'.equation_P)

def BorelRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelRing p a →+* T :=
  IsLocalization.Away.lift (borelDenom p a) (g := BorelPRing.lift p a φ D' hD' hxQ)
    (by rw [BorelPRing.lift_borelDenom]; exact hD'.isUnit_indepElt_PQ.mul hD'.isUnit_indepElt_QP)

end Borel

end LevelP

end ModularCurve

end
