import Lemma.ModularCurve.GlueData
import Lemma.ModularCurve.SupersingularNodePlaces
import Lemma.ModularCurve.CoeffSemilinearAut
import Lemma.ModularCurve.AtkinLehnerPartial
import Lemma.ModularCurve.CuspidalClass
import Lemma.ModularCurve.X0ModL
import Lemma.ModularCurve.CharPReduction
import Lemma.AlgebraicCurve.RegularProlongation
import Lemma.AlgebraicCurve.Repartitions
import Structure.ModularCurve_ProlongationTuple
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

namespace ProlongationTuple


def jFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩

def jQFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (N * q) (dvd_mul_left q N))⟩

def tInfty (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  jQFun N q / jFun N q ^ q

def tZero (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  jFun N q / jQFun N q ^ q

def IsCuspidal (_P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ a : A, W.ord (jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

def IsCuspidal' (_P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  ∀ a : A, W.ord (jQFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

def IsInftySide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsCuspidal P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tInfty N q) (τ : AlgebraicClosure ℚ)

def IsZeroSide (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (tZero N q) (τ : AlgebraicClosure ℚ)

end ProlongationTuple

set_option linter.unusedVariables false in


namespace ProlongationTuple

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem mem_integers₂_iff (f : modularFunctionFieldBar (N * q)) :
    f ∈ R.R₂.integers ↔ atkinLehnerBar N q f ∈ R.R₁.integers := by
  rw [R.mem_integersSnd_iff f, R.mem_integersFst_iff (atkinLehnerBar N q f)]


@[simp] theorem residue₁_apply (f : R.R₁.integers) : R.residue₁ f = R.ι (R.R₁.residue f) := rfl
@[simp] theorem residue₂_apply (f : R.R₂.integers) : R.residue₂ f = R.ι (R.R₂.residue f) := rfl

open Classical in

def DivisorLawFst : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v = v.ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def DivisorLawSnd : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) v = v.ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def OrderLawFixed : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        Finsupp.mapDomain P.reduceFst D v =
          v.ord (R.residue₁ ⟨f, h₁⟩)
            + (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)

open Classical in

def CuspLawInfty : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsInftySide P c →
        Finsupp.mapDomain P.reduceFst (D.filter (IsInftySide P)) (P.reduceFst c) =
          (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩)

open Classical in

def CuspLawZero : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        IsZeroSide P c →
        Finsupp.mapDomain P.reduceSnd (D.filter (IsZeroSide P)) (P.reduceSnd c) =
          (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩)

def IsModel : Prop := R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero

def NodeValueLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ ≠ 0 →
    ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), V.ord f ≠ 0 →
        ¬ (P.reduceFst V = s.1 ∧ P.reduceSnd V = s.2)) →
      ∃ c : k, c ≠ 0 ∧
        s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
        s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c

def RegularityLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (v : Place k (modularFunctionFieldC k N)),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.reduceFst V = v → 0 ≤ V.ord f) →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.reduceFst V = s.1 → 0 ≤ V.ord f) →
      ∃ c : k, s.1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) c ∧
               s.2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) c)

open Classical in

def SplitDatum [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
    (lam : Place k (modularFunctionFieldC k N) → k) : Prop :=
  (∀ w ∈ W, w.ord (π w) = 1) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      Finsupp.mapDomain P.reduceFst (E.filter fun V => E V < 0) v ≤ D₁ v ∧
      D₁ v ≤ Finsupp.mapDomain P.reduceFst (E.filter fun V => 0 < E V) v ∧
      Finsupp.mapDomain P.reduceFst (E.filter fun V => E V < 0) v
        ≤ D₂ (frobOnPlacesGeomLevel k N data hKr v) ∧
      D₂ (frobOnPlacesGeomLevel k N data hKr v)
        ≤ Finsupp.mapDomain P.reduceFst (E.filter fun V => 0 < E V) v) ∧

  D₁.degree + D₂.degree = E.degree ∧

  (∀ w ∈ W, lam w ≠ 0) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
      D₁ v = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v ∧
      D₂ v = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v) ∧

  (∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      D₁ v + D₂ (frobOnPlacesGeomLevel k N data hKr v) = Finsupp.mapDomain P.reduceFst E v) ∧

  (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsInftySide P c →
      D₁ (P.reduceFst c) =
        Finsupp.mapDomain P.reduceFst (E.filter (IsInftySide P)) (P.reduceFst c)) ∧
  (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsZeroSide P c →
      D₂ (P.reduceSnd c) =
        Finsupp.mapDomain P.reduceSnd (E.filter (IsZeroSide P)) (P.reduceSnd c)) ∧

  ∀ f : modularFunctionFieldBar (N * q), f ∈ riemannRochSpace E →
    ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) ∈ riemannRochSpace D₁ ∧
      (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N) ∈ riemannRochSpace D₂ ∧
      ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        ∃ c : k,
          s.1.HasValue (π s.1 ^ (D₁ s.1) * (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N))
            (lam s.1 * c) ∧
          s.2.HasValue ((arithFrobC q k N • π s.1) ^ (D₂ s.2)
              * (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)) c

open Classical in

def SplitLaw [PerfectField k] (W Wbad : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) : Prop :=
  ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) →
    (∀ V ∈ E.support, ∀ w ∈ Wbad, ¬ (P.reduceFst V = w)) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
      (lam : Place k (modularFunctionFieldC k N) → k), R.SplitDatum W π E D₁ D₂ lam

open Classical in

def SplitLawEff [PerfectField k] (W Wbad : Finset (Place k (modularFunctionFieldC k N)))
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) : Prop :=
  ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    (∀ V, 0 ≤ E V) →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) →
    (∀ V ∈ E.support, ∀ w ∈ Wbad, ¬ (P.reduceFst V = w)) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
      (lam : Place k (modularFunctionFieldC k N) → k), R.SplitDatum W π E D₁ D₂ lam

set_option linter.unusedVariables false in


end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
