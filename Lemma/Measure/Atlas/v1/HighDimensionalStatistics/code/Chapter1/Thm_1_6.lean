import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
open MeasureTheory ProbabilityTheory Real BigOperators Finset


/--
[theorem_1_6_subgaussian_vector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_6.lean)
-/
@[path]
private lemma theorem_1_6_subgaussian_vector_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {σsq : ℝ}
  {a : Fin n → ℝ}
-- given
  (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
  (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
  (hX_meas : ∀ i, Measurable (X i)) :
-- imply
  IsSubGaussian (fun ω => ∑ i, a i * X i ω) (σsq * ∑ i, a i ^ 2) μ := by
-- proof
  apply theorem_1_6_subgaussian_vector hX_sg hX_indep hX_meas a


-- created on 2026-10-23
