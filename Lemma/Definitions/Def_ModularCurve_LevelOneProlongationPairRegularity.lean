import Mathlib
import Lemma.Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

namespace LevelOneProlongationPair

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

open Classical in

def RegularityLaw (S₀ : Finset k) : Prop :=
  (∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (v : Place k (modularFunctionFieldC k 1)),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), P.redFst W = v → 0 ≤ W.ord f) →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 → 0 ≤ (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
  (∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      ∀ a ∈ S₀, a ^ (q ^ 2) = a →
      (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          P.redFst W = (frobNodePair q a).1 → 0 ≤ W.ord f) →
      ∃ c : k, (frobNodePair q a).1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1) c ∧
               (frobNodePair q a).2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1) c)

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end
