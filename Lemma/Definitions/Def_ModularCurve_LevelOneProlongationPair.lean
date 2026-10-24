import Mathlib
import Lemma.Definitions.Def_ModularCurve_LevelOneGlueData
import Lemma.Definitions.Def_ModularCurve_SupersingularNodes
import Lemma.Definitions.Def_ModularCurve_SupersingularModuli
import Lemma.Definitions.Def_AlgebraicCurve_RegularProlongation
import Lemma.Definitions.Def_ModularCurve_CharPReduction
import Lemma.Definitions.Def_ModularCurve_CuspidalClass
import Lemma.Definitions.Def_ModularCurve_X0ModL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

def LevelOneProlongationPair.NodeValueLaw (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) : Prop :=
  letI := Classical.decEq k
  ∀ (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (a : k) (ha : a ∈ ssJSet q k)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) -
              algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) -
              algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))),
    ∃ c : k, c ≠ 0 ∧
      (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (⟨_, h₂F⟩ : modularFunctionFieldC k 1) c

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 400000 in

structure LevelOneProlongationPair (P : PlaceSpecialization A q 1 data hKr k red hα hβ) where

  redBar : ResidueField A →+* k
  redBar_residue : ∀ a : A, redBar (IsLocalRing.residue A a) = red a

  ι : modularFunctionFieldFullC (ResidueField A) 1 →+* modularFunctionFieldC k 1
  ι_coe : ∀ x : modularFunctionFieldFullC (ResidueField A) 1,
    ((ι x : modularFunctionFieldC k 1) : LaurentSeries k) = coeffMap redBar (x : LaurentSeries (ResidueField A))

  R₁ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  residue₁_coeffMap : ∀ (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y

  mem_integers₂_iff : ∀ f : modularFunctionFieldBar (1 * q),
    f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers

  residue₂_eq : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
    R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (mem_integers₂_iff f).mp h⟩

  residue₁_eq_modularRedLocHom : ∀ (f : modularFunctionFieldBar (1 * q))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
    ∃ h : f ∈ R₁.integers,
      ((ι (R₁.residue ⟨f, h⟩) : modularFunctionFieldC k 1) : LaurentSeries k) =
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨f, hf⟩

def jFun : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

def jqFun : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

def tInfty : modularFunctionFieldBar (1 * q) := jqFun (q := q) / jFun (q := q) ^ (1 * q)

def tZero : modularFunctionFieldBar (1 * q) := jFun (q := q) / jqFun (q := q) ^ (1 * q)

def IsCuspidal (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ a : A, W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

set_option linter.unusedVariables false in

def IsInftySide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  P.IsCuspidal W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tInfty (q := q)) (τ : AlgebraicClosure ℚ)

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in

def IsCuspidal' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

set_option linter.unusedVariables false in

def IsZeroSide (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tZero (q := q)) (τ : AlgebraicClosure ℚ)

namespace LevelOneProlongationPair

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

def residue₁ : R.R₁.integers →+* modularFunctionFieldC k 1 := R.ι.comp R.R₁.residue

def residue₂ : R.R₂.integers →+* modularFunctionFieldC k 1 := R.ι.comp R.R₂.residue

@[simp] theorem residue₁_apply (f : R.R₁.integers) : R.residue₁ f = R.ι (R.R₁.residue f) := rfl
@[simp] theorem residue₂_apply (f : R.R₂.integers) : R.residue₂ f = R.ι (R.R₂.residue f) := rfl

open Classical in

def DivisorLawFst : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
        Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) v = v.ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def DivisorLawSnd : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
        Finsupp.mapDomain P.redSnd (D.filter P.IsStrictTypeTwo) v = v.ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def CuspLawInfty : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      Finsupp.mapDomain P.redFst (D.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) =
        (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def CuspLawZero : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      Finsupp.mapDomain P.redSnd (D.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) =
        (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨f, h₂⟩)

def OrderLawFixed : Prop :=
  ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        v ≠ P.redFst (cuspInftyBar (1 * q)) →
        Finsupp.mapDomain P.redFst D v =
          v.ord (R.residue₁ ⟨f, h₁⟩) + (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩)

def IsModel : Prop := R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
