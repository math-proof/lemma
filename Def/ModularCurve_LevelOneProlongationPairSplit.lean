import Mathlib
import Def.ModularCurve_LevelOneProlongationPair
import Lemma.AlgebraicCurve.Repartitions
import Lemma.ModularCurve.SupersingularNodes
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve

namespace PlaceSpecialization

namespace LevelOneProlongationPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

open Classical in

def SplitDatum (S₀ : Finset k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) : Prop :=

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      Finsupp.mapDomain P.redFst (E.filter fun W => E W < 0) v ≤ D₁ v ∧
      D₁ v ≤ Finsupp.mapDomain P.redFst (E.filter fun W => 0 < E W) v ∧
      Finsupp.mapDomain P.redFst (E.filter fun W => E W < 0) v ≤ D₂ (frobOnPlacesGeomLevel k 1 data hKr v) ∧
      D₂ (frobOnPlacesGeomLevel k 1 data hKr v) ≤ Finsupp.mapDomain P.redFst (E.filter fun W => 0 < E W) v) ∧

  D₁.degree + D₂.degree = E.degree ∧

  (∀ a ∈ S₀, lam a ≠ 0) ∧

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      D₁ v = Finsupp.mapDomain P.redFst (P.fstPart E) v ∧
      D₂ v = Finsupp.mapDomain P.redSnd (P.sndPart E) v) ∧

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      D₁ v + D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = Finsupp.mapDomain P.redFst E v) ∧

  D₁ (P.redFst (cuspInftyBar (1 * q))) =
      Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) ∧
  D₂ (P.redSnd (cuspZeroBar (1 * q))) =
      Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) ∧

  ∀ (f : modularFunctionFieldBar (1 * q)), f ∈ riemannRochSpace E →
    ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace D₁ ∧
      (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace D₂ ∧
      ∀ a ∈ S₀, a ^ (q ^ 2) = a →
        ∃ c : k,
          (frobNodePair q a).1.HasValue
            (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
                - algebraMap k (modularFunctionFieldC k 1) a) ^ (D₁ (frobNodePair q a).1)
              * (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1)) (lam a * c) ∧
          (frobNodePair q a).2.HasValue
            (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
                - algebraMap k (modularFunctionFieldC k 1) (a ^ q)) ^ (D₂ (frobNodePair q a).2)
              * (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1)) c

open Classical in

def SplitLaw (S₀ : Finset k) : Prop :=
  ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))),
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E) →
    (∀ W ∈ E.support, ∀ a ∈ S₀, a ^ (q ^ 2) = a → (a = 0 ∨ a = 1728) →
        P.redFst W ≠ (frobNodePair q a).1) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k), R.SplitDatum S₀ E D₁ D₂ lam

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
