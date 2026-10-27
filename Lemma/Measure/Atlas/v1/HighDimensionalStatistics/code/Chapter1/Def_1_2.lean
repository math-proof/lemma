import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
open MeasureTheory Real


/--
[IsSubGaussian.integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_2.lean)
-/
@[path]
lemma IsSubGaussian.integrable
  (Ω, μ)
  [MeasurableSpace Ω]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
-- given
  (h : IsSubGaussian X σsq μ) :
-- imply
  Integrable X μ :=
-- proof
  h.1

/--
[IsSubGaussian.mean_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_2.lean)
-/
@[path]
lemma IsSubGaussian.mean_zero
  (Ω, μ)
  [MeasurableSpace Ω]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
-- given
  (h : IsSubGaussian X σsq μ) :
-- imply
  ∫ ω, X ω ∂μ = 0 :=
-- proof
  h.2.1

/--
[IsSubGaussian.exp_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_2.lean)
-/
@[path]
lemma IsSubGaussian.exp_integrable
  (Ω, μ)
  [MeasurableSpace Ω]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : ℝ}
-- given
  (h : IsSubGaussian X σsq μ) :
-- imply
  Integrable (fun ω => Real.exp (s * X ω)) μ :=
-- proof
  h.2.2.1 s

/--
[IsSubGaussian.mgf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_2.lean)
-/
@[path]
lemma IsSubGaussian.mgf_bound
  (Ω, μ)
  [MeasurableSpace Ω]
  {X : Ω → ℝ}
  {σsq : ℝ}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : ℝ}
-- given
  (h : IsSubGaussian X σsq μ) :
-- imply
  ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2) :=
-- proof
  h.2.2.2 s


-- created on 2026-10-23
