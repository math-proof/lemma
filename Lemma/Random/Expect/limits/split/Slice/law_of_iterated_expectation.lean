import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : MeasurableSpace Ω}
  {f : Ω → ℝ}
-- given
  (h₀ : m ≤ mΩ) :
-- imply
  ∫ ω, (π[f | m]) ω ∂π = ∫ ω, f ω ∂π :=
-- proof
  integral_condExp (μ := π) h₀


-- created on 2023-03-31
-- updated on 2026-10-17
