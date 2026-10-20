/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean -/

import sympy.atlas.Analysis.Complex.Wiman.CoefficientExponentialFamily
namespace Complex

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The logarithmic radial majorant is twice continuously differentiable. -/
theorem contDiff_two_wimanGrowth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ContDiff ℝ 2 (wimanGrowth f) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext x
    exact wiman_cgf_eq_growth f hf x
  rw [← hcgf]
  have hAnalytic :
      AnalyticOnNhd ℝ
        (ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f)) Set.univ := by
    simpa [integrableExpSet_wimanCoefficientMeasure_eq_univ f hf] using
      (ProbabilityTheory.analyticOnNhd_cgf
        (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f))
  exact hAnalytic.contDiff

/-- The first derivative of the logarithmic majorant is the mean index under the tilted
coefficient distribution. -/
theorem deriv_wimanGrowth_eq_expectation
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (_hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    deriv (wimanGrowth f) x =
      ∫ n : ℕ, (n : ℝ) ∂(wimanTiltedMeasure f x) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext y
    exact wiman_cgf_eq_growth f hf y
  rw [← hcgf]
  simpa only [wimanTiltedMeasure] using
    (ProbabilityTheory.integral_tilted_mul_self
      (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f) (t := x)
      (mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x)).symm

/-- The second derivative of the logarithmic majorant is the variance of the index under the
tilted coefficient distribution. -/
theorem iteratedDeriv_two_wimanGrowth_eq_variance
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (_hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (wimanGrowth f) x =
      ProbabilityTheory.variance
        (fun n : ℕ => (n : ℝ)) (wimanTiltedMeasure f x) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext y
    exact wiman_cgf_eq_growth f hf y
  rw [← hcgf]
  simpa only [wimanTiltedMeasure] using
    (ProbabilityTheory.variance_tilted_mul
      (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f) (t := x)
      (mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x)).symm

/-- The logarithmic radial majorant has nonnegative second derivative. -/
theorem iteratedDeriv_two_wimanGrowth_nonneg
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    0 ≤ iteratedDeriv 2 (wimanGrowth f) x := by
  rw [iteratedDeriv_two_wimanGrowth_eq_variance f hf hne x]
  exact ProbabilityTheory.variance_nonneg _ _

end
