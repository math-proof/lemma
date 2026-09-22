import sympy.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory


@[main, comm]
private lemma main
  [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α}
  {f g : α → E}
-- given
  (hf : Integrable f μ) (hg : Integrable g μ) :
-- imply
  ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
-- proof
  integral_add hf hg


-- created on 2020-06-05
