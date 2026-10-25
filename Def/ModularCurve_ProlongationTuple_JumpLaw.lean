import Def.ModularCurve_ProlongationTuple
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

noncomputable section

namespace GaussJump

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

open Classical in

def JumpLaw (R : ProlongationTuple P) : Prop :=
  ∀ σ ∈ A.inertiaSubgroupIn ℚ,
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    ∀ D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
      (∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f) →
      (R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ = 0 →
          0 < Divisor.degree (D.filter P.IsStrictSnd)) ∧
        (R.R₂.residue ⟨f, h₂⟩ ≠ 0 → R.R₁.residue ⟨f, h₁⟩ = 0 →
          0 < Divisor.degree (D.filter P.IsStrictFst))

end GaussJump

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

namespace ProlongationTuple

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

open Classical in

def OneSidedRegularityLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
      (∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f) →
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
      (∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ = 0 →
          0 < (s.1).ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 → R.residue₁ ⟨f, h₁⟩ = 0 →
          0 < (s.2).ord (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)))

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
