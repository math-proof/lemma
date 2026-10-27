import Mathlib.Probability.ConditionalProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β}
  {s : Set α} {t : Set β}
-- given
  (h₀ : Measurable y)
  (h₁ : MeasurableSet t)
  (h₂ : π[x ⁻¹' s | y ⁻¹' t] = π (x ⁻¹' s)) :
-- imply
  π (y ⁻¹' t ∩ x ⁻¹' s) = π (x ⁻¹' s) * π (y ⁻¹' t) := by
-- proof
  rw [← cond_mul_eq_inter (h₁.preimage h₀), h₂, mul_comm]


-- created on 2020-12-14
-- updated on 2026-10-26
