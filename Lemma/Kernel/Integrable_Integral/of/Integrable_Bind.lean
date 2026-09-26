import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [SFinite μ]
  {κ : Kernel α β} [IsSFiniteKernel κ]
  {f : β → E}
-- given
  (h : Integrable f (μ.bind κ)) :
-- imply
  Integrable (fun a => ∫ x, f x ∂κ a) μ := by
-- proof
  rw [Measure.comp_eq_comp_const_apply] at h
  simpa using h.integral_comp


-- created on 2026-09-26