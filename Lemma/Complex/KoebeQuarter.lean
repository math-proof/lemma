import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.KoebeQuarter

open Complex.KoebeQuarterWanted

/--
[koebe_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/KoebeQuarter.lean)
-/
@[path]
private lemma koebe_quarter_eq
-- given
  (f : ℂ → ℂ)
  (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
  (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
  (h0 : f 0 = 0)
  (hderiv : deriv f 0 = 1) :
-- imply
  Metric.ball (0 : ℂ) (1/4 : ℝ) ⊆ f '' Metric.ball (0 : ℂ) 1 := by
-- proof
  apply koebe_quarter f hf hinj h0 hderiv


-- created on 2026-10-09
