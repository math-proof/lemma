import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : Ω → ℝ}
-- given
  (c : ℝ) :
-- imply
  c * ∫ ω, f ω ∂μ = ∫ ω, c * f ω ∂μ :=
-- proof
  (integral_const_mul c f).symm


-- created on 2026-09-26
