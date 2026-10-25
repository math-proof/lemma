import Mathlib
import sympy.Basic
import Theorem.Analysis.Complex.Wiman.CumulantMoments
open MeasureTheory ProbabilityTheory
open Complex


namespace Complex

/--
[contDiff_two_wimanGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
lemma contDiff_two_wimanGrowth
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ContDiff ℝ 2 (wimanGrowth f) := by
-- proof
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

end Complex

namespace Complex

/--
[deriv_wimanGrowth_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
lemma deriv_wimanGrowth_eq_expectation
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  deriv (wimanGrowth f) x =
    ∫ n : ℕ, (n : ℝ) ∂(wimanTiltedMeasure f x) := by
-- proof
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

end Complex

namespace Complex

/--
[iteratedDeriv_two_wimanGrowth_eq_variance](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
lemma iteratedDeriv_two_wimanGrowth_eq_variance
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  iteratedDeriv 2 (wimanGrowth f) x =
    ProbabilityTheory.variance
    (fun n : ℕ => (n : ℝ)) (wimanTiltedMeasure f x) := by
-- proof
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

end Complex

namespace Complex

/--
[iteratedDeriv_two_wimanGrowth_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
lemma iteratedDeriv_two_wimanGrowth_nonneg
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  0 ≤ iteratedDeriv 2 (wimanGrowth f) x := by
-- proof
  rw [iteratedDeriv_two_wimanGrowth_eq_variance f hf hne x]
  exact ProbabilityTheory.variance_nonneg _ _
end



-- created on 2026-10-20
-- updated on 2026-10-23
