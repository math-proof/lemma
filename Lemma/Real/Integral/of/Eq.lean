import Mathlib.MeasureTheory.Integral.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {μ ν : Measure α}
  {f : α → β}
-- given
  (hμν : μ = ν) :
-- imply
  ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
-- proof
  rw [hμν]


-- created on 2026-09-18
