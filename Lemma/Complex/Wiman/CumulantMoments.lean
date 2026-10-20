import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.CumulantMoments
open MeasureTheory ProbabilityTheory
open Complex


/--
[contDiff_two_wimanGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
private lemma contDiff_two_wimanGrowth_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ContDiff ℝ 2 (wimanGrowth f) := by
-- proof
  apply Complex.contDiff_two_wimanGrowth f hf

/--
[deriv_wimanGrowth_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
private lemma deriv_wimanGrowth_eq_expectation_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  deriv (wimanGrowth f) x =
    ∫ n : ℕ, (n : ℝ) ∂(wimanTiltedMeasure f x) := by
-- proof
  apply Complex.deriv_wimanGrowth_eq_expectation f hf hne x

/--
[iteratedDeriv_two_wimanGrowth_eq_variance](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
private lemma iteratedDeriv_two_wimanGrowth_eq_variance_eq
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
  apply Complex.iteratedDeriv_two_wimanGrowth_eq_variance f hf hne x

/--
[iteratedDeriv_two_wimanGrowth_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CumulantMoments.lean)
-/
@[path]
private lemma iteratedDeriv_two_wimanGrowth_nonneg_eq
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  0 ≤ iteratedDeriv 2 (wimanGrowth f) x := by
-- proof
  apply Complex.iteratedDeriv_two_wimanGrowth_nonneg f hf hne x


-- created on 2026-10-20
