import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {μ : Measure S} [IsProbabilityMeasure μ] :
-- imply
  ∑ s, (μ {s}).toReal = 1 := by
-- proof
  simpa [measureReal_def] using sum_measureReal_singleton (μ := μ) Finset.univ


-- created on 2026-09-26