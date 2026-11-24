import Mathlib
import Notation.Algebra.Power
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.OUSemigroup.gaussianSpace.integral_gaussian_sum
open GaussianSpace ProbabilityTheory MeasureTheory Real ContinuousLinearMap Bool


/--
[ornsteinUhlenbeckOp_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {ρ σ : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
  (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
  (hf : Measurable f)
  (hf_int : ∀ (v : EuclideanSpace ℝ (Fin n)), Integrable (fun u => f (v + Real.sqrt (1 - (ρ * σ)²) • u)) (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
-- imply
  ornsteinUhlenbeckOp ρ (fun x => ornsteinUhlenbeckOp σ f x) = ornsteinUhlenbeckOp (ρ * σ) f := by
-- proof
  funext x
  simp only [ornsteinUhlenbeckOp]
  have h_alg : ∀ w v : EuclideanSpace ℝ (Fin n),
    f (σ • (ρ • x + Real.sqrt (1 - ρ²) • w) + Real.sqrt (1 - σ²) • v) =
    f ((ρ * σ) • x + ((σ * Real.sqrt (1 - ρ²)) • w + Real.sqrt (1 - σ²) • v)) := by
    intro w v; congr 1; simp [smul_add, mul_smul, mul_comm ρ σ]; abel
  simp_rw [h_alg]
  set a := σ * Real.sqrt (1 - ρ²)
  set b := Real.sqrt (1 - σ²)
  set c := Real.sqrt (1 - (ρ * σ)²)
  set g := fun z : EuclideanSpace ℝ (Fin n) => f ((ρ * σ) • x + z)
  have hρ2 : ρ² ≤ 1 := by nlinarith [hρ.1, hρ.2]
  have hσ2 : σ² ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have hρσ2 : (ρ * σ)² ≤ 1 := by nlinarith [sq_nonneg ρ, sq_nonneg σ]
  have habc : a² + b² = c² := by
    simp only [a, b, c]
    rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - ρ²)]
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - σ²)]
    rw [show (ρ * σ)² = ρ² * σ² by ring]
    rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - ρ² * σ²)]
    ring
  change ∫ w, ∫ v, g (a • w + b • v) ∂_ ∂_ = ∫ u, g (c • u) ∂_
  have hg_meas : Measurable g := hf.comp (measurable_const.add measurable_id)
  apply integral_gaussian_sum (a := a) (b := b) (c := c) (g := g) habc hg_meas
  rw [← integrable_map_measure hg_meas.aestronglyMeasurable
    (addSmulCLM (E := EuclideanSpace ℝ (Fin n)) a b).continuous.aemeasurable,
    gaussian_sum_pushforward (E := EuclideanSpace ℝ (Fin n)) (a := a) (b := b) (c := c) habc,
    integrable_map_measure hg_meas.aestronglyMeasurable
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).continuous.aemeasurable]
  exact hf_int ((ρ * σ) • x)


lemma GaussianSpace.ornsteinUhlenbeckOp_comp
  {n : ℕ}
  {ρ σ : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
  (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
  (hf : Measurable f)
  (hf_int : ∀ (v : EuclideanSpace ℝ (Fin n)), Integrable (fun u => f (v + Real.sqrt (1 - (ρ * σ)²) • u)) (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
-- imply
  ornsteinUhlenbeckOp ρ (fun x => ornsteinUhlenbeckOp σ f x) = ornsteinUhlenbeckOp (ρ * σ) f :=
-- proof
  main hρ hσ hf hf_int


-- created on 2026-10-23
-- updated on 2026-11-24
