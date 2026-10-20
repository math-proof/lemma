import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.CoefficientExponentialFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Complex


/--
[wimanCoefficientMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wimanCoefficientMeasure_singleton_eq
  {f : ℂ → ℂ}
  {n : ℕ} :
-- imply
  wimanCoefficientMeasure f {n} = ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ := by
-- proof
  apply Complex.wimanCoefficientMeasure_singleton f n

/--
[integrable_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma integrable_exp_mul_wimanCoefficientMeasure_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Integrable (fun n : ℕ => Real.exp (x * (n : ℝ))) (wimanCoefficientMeasure f) := by
-- proof
  apply Complex.integrable_exp_mul_wimanCoefficientMeasure f hf x

/--
[integrableExpSet_wimanCoefficientMeasure_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma integrableExpSet_wimanCoefficientMeasure_eq_univ_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  integrableExpSet (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) = Set.univ := by
-- proof
  apply Complex.integrableExpSet_wimanCoefficientMeasure_eq_univ f hf

/--
[mem_interior_integrableExpSet_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma mem_interior_integrableExpSet_wimanCoefficientMeasure_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  x ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f)) := by
-- proof
  apply Complex.mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x

/--
[integral_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma integral_exp_mul_wimanCoefficientMeasure_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ∫ n : ℕ, Real.exp (x * (n : ℝ)) ∂(wimanCoefficientMeasure f) =
    wimanMajorant f (Real.exp x) := by
-- proof
  apply Complex.integral_exp_mul_wimanCoefficientMeasure f hf x

/--
[wiman_mgf_eq_majorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wiman_mgf_eq_majorant_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  mgf (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) x =
    wimanMajorant f (Real.exp x) := by
-- proof
  apply Complex.wiman_mgf_eq_majorant f hf x

/--
[wiman_cgf_eq_growth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wiman_cgf_eq_growth_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f) x = wimanGrowth f x := by
-- proof
  apply Complex.wiman_cgf_eq_growth f hf x

/--
[wimanCoefficientMeasure_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wimanCoefficientMeasure_ne_zero_eq
  {f : ℂ → ℂ}
-- given
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  wimanCoefficientMeasure f ≠ 0 := by
-- proof
  apply Complex.wimanCoefficientMeasure_ne_zero f hne

/--
[isProbabilityMeasure_wimanTiltedMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma isProbabilityMeasure_wimanTiltedMeasure_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  IsProbabilityMeasure (wimanTiltedMeasure f x) := by
-- proof
  apply Complex.isProbabilityMeasure_wimanTiltedMeasure f hf hne x

/--
[wimanTiltedMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wimanTiltedMeasure_singleton_eq
  {f : ℂ → ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTiltedMeasure f x {n} =
    ENNReal.ofReal
    (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) := by
-- proof
  apply Complex.wimanTiltedMeasure_singleton f hf x n

/--
[wimanTiltedMeasure_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
private lemma wimanTiltedMeasure_eq_sum_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTiltedMeasure f x =
    Measure.sum fun n : ℕ =>
    ENNReal.ofReal
    (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) •
    Measure.dirac n := by
-- proof
  apply Complex.wimanTiltedMeasure_eq_sum f hf x


-- created on 2026-10-20
