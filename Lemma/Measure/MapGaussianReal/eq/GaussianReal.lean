import Mathlib.Probability.Distributions.Gaussian.Real
import Initialize.Tactic.Attr.Basic
import Instance.NNReal.Coe
open MeasureTheory ProbabilityTheory Real
open scoped NNReal


/-- Affine standardization of one Gaussian: (X - μ)/σ ~ N(0,1). -/
@[path]
private lemma main
  {μ : ℝ}
  {σ : ℝ⁺} :
-- imply
  (gaussianReal μ (σ : NNReal)²).map (fun x => (x - μ) / (σ : ℝ)) = (gaussianReal 0 1 : Measure ℝ) := by
-- proof
  -- Free NNReal variable so field_simp matches the old helper.
  suffices h : ∀ {σ : NNReal}, 0 < (σ : ℝ) →
      (gaussianReal μ σ²).map (fun x => (x - μ) / (σ : ℝ)) = gaussianReal 0 1 by
    apply h
    exact σ.property
  intro σ hσ
  have hσ0 : (σ : ℝ) ≠ 0 := hσ.ne'
  have hcomp :
    (fun x : ℝ => (x - μ) / (σ : ℝ)) =
        (fun z : ℝ => (σ : ℝ)⁻¹ * z) ∘ (fun x : ℝ => x + (-μ)) := by
    funext x
    simp [sub_eq_add_neg, div_eq_inv_mul, mul_comm]
  rw [hcomp]
  rw [← Measure.map_map (measurable_const_mul _) (measurable_add_const _)]
  have hadd := gaussianReal_map_add_const (μ := μ) (v := σ²) (-μ)
  simp only [add_neg_cancel] at hadd
  rw [hadd]
  have hmul := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := σ²) (σ : ℝ)⁻¹
  rw [hmul, mul_zero]
  congr 1
  refine NNReal.eq ?_
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, pow_two]
  field_simp [hσ0]


-- created on 2026-10-31
