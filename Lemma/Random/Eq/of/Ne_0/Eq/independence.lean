import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β}
  {s : Set α} {t : Set β}
-- given
  (h₀ : x ⟂ᵢ[π] y)
  (h₁ : Measurable x)
  (h₂ : MeasurableSet s)
  (h₃ : MeasurableSet t)
  (h₄ : π (x ⁻¹' s) ≠ 0) :
-- imply
  π[y ⁻¹' t | x ⁻¹' s] = π (y ⁻¹' t) := by
-- proof
  rw [cond_apply (h₂.preimage h₁), h₀.measure_inter_preimage_eq_mul s t h₂ h₃]
  exact ENNReal.inv_mul_cancel_left h₄ (measure_ne_top π _)


-- created on 2021-08-08
-- updated on 2026-10-17
