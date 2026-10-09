import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.FatouRadial

open Complex.FatouRadialWanted
open MeasureTheory Set Filter

/--
[fatou_radial_limit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/FatouRadial.lean)
-/
@[path]
private lemma fatou_radial_limit_eq
-- given
  (f : ℂ → ℂ)
  (hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
  (hf_bdd : ∃ M : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
-- imply
  ∀ᵐ θ : ℝ ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
    ∃ L : ℂ,
      Filter.Tendsto (fun r : ℝ =>
        f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds L) := by
-- proof
  apply fatou_radial_limit f hf_diff hf_bdd


-- created on 2026-10-09
