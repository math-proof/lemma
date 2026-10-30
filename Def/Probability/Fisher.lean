import Mathlib.Probability.Distributions.Beta
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal


/-- Probability density of the Fisher–Snedecor F-distribution with `d₁`, `d₂` degrees of
freedom (textbook / sympy `fisher_snedecor.pdf`):
`pdf(x) = (d₁/d₂)^(d₁/2) / B(d₁/2, d₂/2) * x^(d₁/2 - 1) * (1 + (d₁/d₂)·x)^(-(d₁+d₂)/2)`
for `x > 0`, else `0`. Uses Mathlib `ProbabilityTheory.beta` for the beta function. -/
noncomputable def fisherPDFReal (d₁ d₂ : ℕ) (x : ℝ) : ℝ :=
  if 0 < x then
    let α : ℝ := (d₁ : ℝ) / 2
    let β : ℝ := (d₂ : ℝ) / 2
    ((d₁ : ℝ) / d₂) ^ α / beta α β * x ^ (α - 1) *
      (1 + ((d₁ : ℝ) / d₂) * x) ^ (-(α + β))
  else
    0


/-- ENNReal-valued Fisher–Snedecor pdf. -/
noncomputable def fisherPDF (d₁ d₂ : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fisherPDFReal d₁ d₂ x)


/-- Map sending a Beta(`α`,`β`) sample `y ∈ (0,1)` to the corresponding F-ratio
`(β/α) · (y / (1 - y))` (beta-prime scaled to Fisher–Snedecor).
Defined for all `ℝ` (at `y = 1`, Lean `Real` division by zero yields `0`). -/
noncomputable def fisherOfBeta (d₁ d₂ : ℕ) (y : ℝ) : ℝ :=
  ((d₂ : ℝ) / d₁) * (y / (1 - y))


/-- The Fisher–Snedecor F-distribution with `d₁`, `d₂` degrees of freedom on `ℝ`.

Textbook characterization via Beta: if `Y ∼ Beta(d₁/2, d₂/2)`, then
`(d₂/d₁) · (Y/(1-Y)) ∼ F(d₁, d₂)`.

Edge cases: if `d₁ = 0` or `d₂ = 0` this is `Measure.dirac 0` (degenerate /
undefined classical F; mirrors `chiSquaredReal 0 = dirac 0`). -/
noncomputable def fisherReal (d₁ d₂ : ℕ) : Measure ℝ :=
  if d₁ = 0 ∨ d₂ = 0 then
    Measure.dirac 0
  else
    (betaMeasure ((d₁ : ℝ) / 2) ((d₂ : ℝ) / 2)).map (fisherOfBeta d₁ d₂)


/-- Density form of `fisherReal` (Lebesgue `withDensity` of the textbook pdf).
Equals `fisherReal` for `d₁, d₂ > 0` (characterization left for later lemmas).
For `d₁ = 0` or `d₂ = 0` this is still the pdf-based measure (typically not a
probability measure); prefer `fisherReal` for the probability measure API. -/
noncomputable def fisherReal_withDensity (d₁ d₂ : ℕ) : Measure ℝ :=
  volume.withDensity (fisherPDF d₁ d₂)


instance instIsProbabilityMeasureFisherReal (d₁ d₂ : ℕ) :
    IsProbabilityMeasure (fisherReal d₁ d₂) := by
  by_cases h : d₁ = 0 ∨ d₂ = 0
  · simpa [fisherReal, h] using
      (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · have hd1 : d₁ ≠ 0 := fun h1 ↦ h (Or.inl h1)
    have hd2 : d₂ ≠ 0 := fun h2 ↦ h (Or.inr h2)
    have ha : 0 < (d₁ : ℝ) / 2 := by
      have : (0 : ℕ) < d₁ := Nat.pos_of_ne_zero hd1
      positivity
    have hb : 0 < (d₂ : ℝ) / 2 := by
      have : (0 : ℕ) < d₂ := Nat.pos_of_ne_zero hd2
      positivity
    have _hβ : IsProbabilityMeasure (betaMeasure ((d₁ : ℝ) / 2) ((d₂ : ℝ) / 2)) :=
      isProbabilityMeasureBeta ha hb
    simpa [fisherReal, h] using
      (inferInstance : IsProbabilityMeasure
        ((betaMeasure ((d₁ : ℝ) / 2) ((d₂ : ℝ) / 2)).map (fisherOfBeta d₁ d₂)))
