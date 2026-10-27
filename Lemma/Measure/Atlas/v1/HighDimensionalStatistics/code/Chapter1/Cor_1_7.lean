import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Cor_1_7
open MeasureTheory Real ProbabilityTheory BigOperators Finset


/--
[corollary_1_7_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Cor_1_7.lean)
-/
@[path]
private lemma corollary_1_7_upper_tail_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {σsq : ℝ}
  {a : Fin n → ℝ}
  {t : ℝ}
-- given
  (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
  (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
  (hX_meas : ∀ i, Measurable (X i))
  (ht : 0 < t) :
-- imply
  μ {ω | (∑ i, a i * X i ω) > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) := by
-- proof
  apply corollary_1_7_upper_tail hX_sg hX_indep hX_meas a t ht

/--
[corollary_1_7_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Cor_1_7.lean)
-/
@[path]
private lemma corollary_1_7_lower_tail_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {σsq : ℝ}
  {a : Fin n → ℝ}
  {t : ℝ}
-- given
  (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
  (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
  (hX_meas : ∀ i, Measurable (X i))
  (ht : 0 < t) :
-- imply
  μ {ω | (∑ i, a i * X i ω) < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) := by
-- proof
  apply corollary_1_7_lower_tail hX_sg hX_indep hX_meas a t ht

/--
[corollary_1_7_linear_combination_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Cor_1_7.lean)
-/
@[path]
private lemma corollary_1_7_linear_combination_tail_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {σsq : ℝ}
  {a : Fin n → ℝ}
  {t : ℝ}
-- given
  (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
  (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
  (hX_meas : ∀ i, Measurable (X i))
  (ht : 0 < t) :
-- imply
  μ {ω | (∑ i, a i * X i ω) > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) ∧ μ {ω | (∑ i, a i * X i ω) < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) := by
-- proof
  apply corollary_1_7_linear_combination_tail hX_sg hX_indep hX_meas a t ht


-- created on 2026-10-23
