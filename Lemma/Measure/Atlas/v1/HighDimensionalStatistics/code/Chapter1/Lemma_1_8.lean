import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
open MeasureTheory Real ProbabilityTheory Set


/--
[hoeffding_mgf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_8.lean)
-/
@[path]
private lemma hoeffding_mgf_bound_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {a b : ℝ}
  {s : ℝ}
-- given
  (hab : a < b)
  (hXm : Measurable X)
  (hXa : ∀ᵐ ω ∂μ, a ≤ X ω)
  (hXb : ∀ᵐ ω ∂μ, X ω ≤ b)
  (hmean : ∫ ω, X ω ∂μ = 0) :
-- imply
  ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
-- proof
  apply hoeffding_mgf_bound hab hXm hXa hXb hmean s

/--
[lemma_1_8_hoeffding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_8.lean)
-/
@[path]
private lemma lemma_1_8_hoeffding_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hXm : Measurable X)
  (hXi : Integrable X μ)
  (hXa : ∀ᵐ ω ∂μ, a ≤ X ω)
  (hXb : ∀ᵐ ω ∂μ, X ω ≤ b)
  (hmean : ∫ ω, X ω ∂μ = 0) :
-- imply
  IsSubGaussian X ((b - a) ^ 2 / 4) μ := by
-- proof
  apply lemma_1_8_hoeffding hab hXm hXi hXa hXb hmean


-- created on 2026-10-23
