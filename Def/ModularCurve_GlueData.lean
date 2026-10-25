import Instance.ModularCurve_JZeroSemistableSpecialization
import Structure.ModularCurve_PlaceSpecialization

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

def reduceFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Place k (modularFunctionFieldC k N) :=
  P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)

def reduceSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Place k (modularFunctionFieldC k N) :=
  P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)

def IsStrictFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W ∧
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W))
      ≠ P.reduceFst W

def IsStrictSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) ∧
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))
      ≠ P.reduceSnd W

def IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ W ∈ D.support, P.IsStrictFst W ∨ P.IsStrictSnd W

open Classical in

def fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
  D.filter P.IsStrictFst

open Classical in

def sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
  D.filter P.IsStrictSnd

def glueData
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    GluingData k (modularFunctionFieldC k N) S :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D), Finsupp.mapDomain P.reduceSnd (P.sndDiv D), 0)

def IsGluedSpecialization
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (sp : ↥(inertiaInvariants A (N * q)) →+ GluedPic0 k (modularFunctionFieldC k N) S) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (N * q))
    (x : ↥(GluingData.admissible S)),
    P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
    (x : GluingData k (modularFunctionFieldC k N) S) = P.glueData S D →
      sp ⟨Pic0.mk D, hH⟩ = GluedPic0.mk S x

def IsGoodClass
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (x : JZero (N * q)) : Prop :=
  ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
    P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
      P.glueData S D ∈ GluingData.admissible S ∧ Pic0.mk D = x

end PlaceSpecialization

end ModularCurve

end
