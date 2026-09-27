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
  ∫ x, f x ∂μ.bind κ = ∫ a, ∫ x, f x ∂κ a ∂μ := by
-- proof
  rw [Measure.comp_eq_comp_const_apply] at h ⊢
  rw [Kernel.integral_comp h, Kernel.const_apply]


-- created on 2026-09-26