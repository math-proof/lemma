module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Real

public section

open MeasureTheory


public theorem Random.Sum_ToReal.eq.One
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {μ : Measure S} [IsProbabilityMeasure μ] :
-- imply
  ∑ s, (μ {s}).toReal = 1 := by
-- proof
  simpa [measureReal_def] using sum_measureReal_singleton (μ := μ) Finset.univ


-- created on 2026-09-26
