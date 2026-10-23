import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.OUSemigroup
open GaussianSpace ProbabilityTheory MeasureTheory


/--
[gaussian_sum_pushforward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma gaussian_sum_pushforward_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {a b c : ℝ}
-- given
  (habc : a ^ 2 + b ^ 2 = c ^ 2) :
-- imply
  ((stdGaussian E).prod (stdGaussian E)).map (addSmulCLM a b) = (stdGaussian E).map (c • ContinuousLinearMap.id ℝ E) := by
-- proof
  apply GaussianSpace.gaussian_sum_pushforward a b c habc

/--
[integral_gaussian_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma integral_gaussian_sum_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {a b c : ℝ}
  {g : E → ℝ}
-- given
  (habc : a ^ 2 + b ^ 2 = c ^ 2)
  (hg_meas : Measurable g)
  (hg_int : Integrable (g ∘ (addSmulCLM (E := E) a b)) ((stdGaussian E).prod (stdGaussian E))) :
-- imply
  ∫ w, ∫ v, g (a • w + b • v) ∂(stdGaussian E) ∂(stdGaussian E) = ∫ u, g (c • u) ∂(stdGaussian E) := by
-- proof
  apply GaussianSpace.integral_gaussian_sum a b c habc g hg_meas hg_int

/--
[ornsteinUhlenbeckOp_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma ornsteinUhlenbeckOp_comp_eq
  {n : ℕ}
  {ρ σ : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
  (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
  (hf : Measurable f)
  (hf_int : ∀ (v : EuclideanSpace ℝ (Fin n)), Integrable (fun u => f (v + Real.sqrt (1 - (ρ * σ) ^ 2) • u)) (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
-- imply
  ornsteinUhlenbeckOp ρ (fun x => ornsteinUhlenbeckOp σ f x) = ornsteinUhlenbeckOp (ρ * σ) f := by
-- proof
  apply GaussianSpace.ornsteinUhlenbeckOp_comp ρ σ hρ hσ f hf hf_int


-- created on 2026-10-23
