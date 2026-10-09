import sympy.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory


@[path, comm]
private lemma smul
  [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α}
  {f : α → E} (c : ℝ) :
-- imply
  ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ :=
-- proof
  integral_smul c f


@[path, comm]
private lemma main
  [MeasurableSpace α]
  {μ : Measure α}
  {f : α → ℝ} (c : ℝ) :
-- imply
  ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ :=
-- proof
  integral_smul c f


-- created on 2026-09-19
