import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
open MeasureTheory Real ProbabilityTheory SubGaussian


namespace SubGaussian

/--
[subGaussian_tail_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_3.lean)
-/
@[path]
lemma subGaussian_tail_bounds
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hX : IsSubGaussian X σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | X ω > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) ∧ μ {ω | X ω < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
-- proof
  ⟨lemma_1_3_upper_tail hX t ht, lemma_1_3_lower_tail hX t ht⟩
end SubGaussian
export SubGaussian (lemma_1_3_upper_tail lemma_1_3_lower_tail subGaussian_tail_bounds)


/--
[lemma_1_3_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_3.lean)
-/
@[path]
private lemma lemma_1_3_upper_tail_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hX : IsSubGaussian X σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | X ω > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
-- proof
  apply SubGaussian.lemma_1_3_upper_tail hX t ht

/--
[lemma_1_3_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_3.lean)
-/
@[path]
private lemma lemma_1_3_lower_tail_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hX : IsSubGaussian X σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | X ω < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
-- proof
  apply SubGaussian.lemma_1_3_lower_tail hX t ht


-- created on 2026-10-23
