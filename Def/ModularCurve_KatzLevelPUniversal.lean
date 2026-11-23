import Mathlib
import Def.ModularCurve_KatzLevelP
import Instance.ModularCurve_KatzLevelPUniversal

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section TorsionPoint

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

def PsiRoot : Type u := AdjoinRoot (W.preΨ p)

def PsiRoot.ofBase : B →+* PsiRoot W p := AdjoinRoot.of (W.preΨ p)

def psiRootX : PsiRoot W p := AdjoinRoot.root (W.preΨ p)

def torsionQuadratic : Polynomial (PsiRoot W p) :=
  X ^ 2 + C (PsiRoot.ofBase W p W.a₁ * psiRootX W p + PsiRoot.ofBase W p W.a₃) * X -
    C (psiRootX W p ^ 3 + PsiRoot.ofBase W p W.a₂ * psiRootX W p ^ 2 +
      PsiRoot.ofBase W p W.a₄ * psiRootX W p + PsiRoot.ofBase W p W.a₆)

def TorsionPointRing : Type u := AdjoinRoot (torsionQuadratic W p)

def TorsionPointRing.ofPsiRoot : PsiRoot W p →+* TorsionPointRing W p :=
  AdjoinRoot.of (torsionQuadratic W p)

def TorsionPointRing.ofBase : B →+* TorsionPointRing W p :=
  (TorsionPointRing.ofPsiRoot W p).comp (PsiRoot.ofBase W p)

def torsionPtX : TorsionPointRing W p := TorsionPointRing.ofPsiRoot W p (psiRootX W p)

def torsionPtY : TorsionPointRing W p := AdjoinRoot.root (torsionQuadratic W p)

def torsionPtCurve : WeierstrassCurve (TorsionPointRing W p) :=
  W.map (TorsionPointRing.ofBase W p)

end TorsionPoint

section TwoPoints

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

abbrev TwoPointRing : Type u := TorsionPointRing (torsionPtCurve W p) p

abbrev TwoPointRing.ofOnePoint : TorsionPointRing W p →+* TwoPointRing W p :=
  TorsionPointRing.ofBase (torsionPtCurve W p) p

def TwoPointRing.ofBase : B →+* TwoPointRing W p :=
  (TwoPointRing.ofOnePoint W p).comp (TorsionPointRing.ofBase W p)

abbrev twoPointCurve : WeierstrassCurve (TwoPointRing W p) := torsionPtCurve (torsionPtCurve W p) p

def TwoPointRing.xP : TwoPointRing W p := TwoPointRing.ofOnePoint W p (torsionPtX W p)

def TwoPointRing.yP : TwoPointRing W p := TwoPointRing.ofOnePoint W p (torsionPtY W p)

def TwoPointRing.xQ : TwoPointRing W p := torsionPtX (torsionPtCurve W p) p

def TwoPointRing.yQ : TwoPointRing W p := torsionPtY (torsionPtCurve W p) p

def indepDenom : TwoPointRing W p :=
  indepElt (twoPointCurve W p) p (TwoPointRing.xP W p) (TwoPointRing.xQ W p) *
    indepElt (twoPointCurve W p) p (TwoPointRing.xQ W p) (TwoPointRing.xP W p)

def BasisRing : Type u := Localization.Away (indepDenom W p)

def BasisRing.ofTwoPoint : TwoPointRing W p →+* BasisRing W p :=
  algebraMap (TwoPointRing W p) (BasisRing W p)

def BasisRing.ofBase : B →+* BasisRing W p :=
  (BasisRing.ofTwoPoint W p).comp (TwoPointRing.ofBase W p)

def basisCurve : WeierstrassCurve (BasisRing W p) := W.map (BasisRing.ofBase W p)

def basisData : LevelPData (BasisRing W p) where
  xP := BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)
  yP := BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)
  xQ := BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)
  yQ := BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)

end TwoPoints

def genericCurve : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

variable (p : ℕ)

def pDelta : MvPolynomial (Fin 5) ℤ := (p : MvPolynomial (Fin 5) ℤ) * genericCurve.Δ

def UnivBase : Type := Localization.Away (pDelta p)

def univCurve : WeierstrassCurve (UnivBase p) :=
  genericCurve.map (algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p))

abbrev UnivOnePoint : Type := TorsionPointRing (univCurve p) p

abbrev UnivTwoPoint : Type := TwoPointRing (univCurve p) p

abbrev UnivBasisRing : Type := BasisRing (univCurve p) p

abbrev UnivBasisRing.ofBase : UnivBase p →+* UnivBasisRing p := BasisRing.ofBase (univCurve p) p

abbrev univCurveT : WeierstrassCurve (UnivBasisRing p) := basisCurve (univCurve p) p

abbrev univData : LevelPData (UnivBasisRing p) := basisData (univCurve p) p

end LevelP

namespace KatzLevelPForm

open scoped TensorProduct

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}

def univInclude (R : Type u) [CommRing R] (p : ℕ) :
    LevelP.UnivBasisRing p →+* R ⊗[ℤ] LevelP.UnivBasisRing p :=
  (Algebra.TensorProduct.includeRight :
    LevelP.UnivBasisRing p →ₐ[ℤ] R ⊗[ℤ] LevelP.UnivBasisRing p).toRingHom

def univCurveOver (R : Type u) [CommRing R] (p : ℕ) :
    WeierstrassCurve (R ⊗[ℤ] LevelP.UnivBasisRing p) :=
  (LevelP.univCurveT p).map (univInclude R p)

def univDataOver (R : Type u) [CommRing R] (p : ℕ) :
    LevelPData (R ⊗[ℤ] LevelP.UnivBasisRing p) :=
  (LevelP.univData p).map (univInclude R p)

def evalUniv (F : KatzLevelPForm R p k) : R ⊗[ℤ] LevelP.UnivBasisRing p :=
  F.toFun (univCurveOver R p) (isUnit_Δ_univCurveOver R p) (univDataOver R p)
    (isLevelPStructure_univDataOver R p)

end KatzLevelPForm

end ModularCurve

end
