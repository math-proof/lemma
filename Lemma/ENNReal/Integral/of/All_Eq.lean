import sympy.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory


@[main]
private lemma main
  {α : Type*}
  [MeasurableSpace α]
  {μ : Measure α}
  {f g : α → ENNReal}
-- given
  (h : ∀ x : α, f x = g x) :
-- imply
  ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ :=
-- proof
  lintegral_congr_ae (ae_of_all μ h)


-- created on 2026-09-14
