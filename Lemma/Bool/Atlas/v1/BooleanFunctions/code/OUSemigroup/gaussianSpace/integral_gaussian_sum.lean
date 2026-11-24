import Mathlib
import Notation.Algebra.Power
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.OUSemigroup.gaussianSpace.gaussian_sum_pushforward
open GaussianSpace ProbabilityTheory MeasureTheory Real ContinuousLinearMap Bool


/--
[integral_gaussian_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a b c : ℝ}
  {g : E → ℝ}
-- given
  (habc : a² + b² = c²)
  (hg_meas : Measurable g)
  (hg_int : Integrable (g ∘ addSmulCLM (E := E) a b) ((stdGaussian E).prod (stdGaussian E))) :
-- imply
  ∫ w, ∫ v, g (a • w + b • v) ∂(stdGaussian E) ∂(stdGaussian E) = ∫ u, g (c • u) ∂(stdGaussian E) := by
-- proof
  have h_eq : ∀ w v, g (a • w + b • v) = (g ∘ addSmulCLM (E := E) a b) (w, v) := by
    intro w v; simp [addSmulCLM, Function.comp]
  simp_rw [h_eq]
  rw [← integral_prod _ hg_int]
  simp only [Function.comp]
  rw [← integral_map (by fun_prop : AEMeasurable (addSmulCLM (E := E) a b) _)
    hg_meas.aestronglyMeasurable]
  rw [gaussian_sum_pushforward habc]
  rw [integral_map (by fun_prop : AEMeasurable (c • ContinuousLinearMap.id ℝ E) (stdGaussian E))
    hg_meas.aestronglyMeasurable]
  simp


lemma GaussianSpace.integral_gaussian_sum
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a b c : ℝ}
  {g : E → ℝ}
-- given
  (habc : a² + b² = c²)
  (hg_meas : Measurable g)
  (hg_int : Integrable (g ∘ addSmulCLM (E := E) a b) ((stdGaussian E).prod (stdGaussian E))) :
-- imply
  ∫ w, ∫ v, g (a • w + b • v) ∂(stdGaussian E) ∂(stdGaussian E) = ∫ u, g (c • u) ∂(stdGaussian E) :=
-- proof
  main habc hg_meas hg_int


-- created on 2026-10-23
-- updated on 2026-11-24
