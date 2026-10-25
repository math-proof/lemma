import Mathlib
import Def.ModularCurve_LevelOneProlongationPairSplit
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

def SplitLawEff (S₀ : Finset k) : Prop :=
  ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))),
    (∀ W, 0 ≤ E W) →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E) →
    (∀ W ∈ E.support, ∀ a ∈ S₀, a ^ (q ^ 2) = a → (a = 0 ∨ a = 1728) →
        P.redFst W ≠ (frobNodePair q a).1) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k), R.SplitDatum S₀ E D₁ D₂ lam

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
