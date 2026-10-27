import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m₁ m₂ : MeasurableSpace Ω}
  {f : Ω → ℝ}
-- given
  (h₀ : m₁ ≤ m₂)
  (h₁ : m₂ ≤ mΩ) :
-- imply
  π[π[f | m₂] | m₁] =ᵐ[π] π[f | m₁] :=
-- proof
  condExp_condExp_of_le (μ := π) h₀ h₁


-- created on 2023-04-22
-- updated on 2026-10-26
