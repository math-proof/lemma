import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {s : Finset ι}
  {f : ι → Ω → ℝ}
-- given
  (h : ∀ i ∈ s, Integrable (f i) μ) :
-- imply
  ∑ i ∈ s, ∫ ω, f i ω ∂μ = ∫ ω, ∑ i ∈ s, f i ω ∂μ :=
-- proof
  (integral_finsetSum s h).symm


-- created on 2026-09-26
