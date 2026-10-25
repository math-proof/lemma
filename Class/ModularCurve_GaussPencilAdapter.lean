import Structure.ModularCurve_LevelOneProlongationPair

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve ModularCurve

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
  {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
  [Algebra K₁ (modularFunctionFieldBar (1 * q))]
  [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]

variable (R : LevelOneProlongationPair P)

variable (K₁) in
class HasGaussTransport : Prop where
  mem₂_of_mem₁ : ∀ x : K₁, algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₁.integers →
    algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers
  mem₁_of_mem₂ : ∀ x : K₁, algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₂.integers →
    algebraMap K₁ (modularFunctionFieldBar (1 * q)) x ∈ R.R₁.integers

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
