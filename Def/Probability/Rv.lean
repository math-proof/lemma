module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Class.Probability.Rv

@[expose] public section

open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite


/-- Build a `ReferenceMeasure` from an explicit σ-finite measure. -/
@[instance_reducible]
def ReferenceMeasure.of {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : ReferenceMeasure α where
  toMeasurableSpace := inferInstance
  measure := μ
  toSigmaFinite := inferInstance

