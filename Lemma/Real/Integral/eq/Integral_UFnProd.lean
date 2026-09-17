import sympy.Basic
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [SFinite μ] [SFinite ν]
  {f : α × β → E}
-- given
  (hf : Integrable f (μ.prod ν)) :
-- imply
  ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
-- proof
  integral_prod f hf


-- created on 2026-09-17
