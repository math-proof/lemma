module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Def.Probability.Rv

@[expose] public section

open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite


/--
The product of two state measure spaces is a state measure space on `α × β`, whose state
measure is the product measure. This lets a joint random variable `(x, y) : Ω → α × β`
follow an ordinary `Distribution π ρ` via `~`, with the product measure as the state measure.
-/
noncomputable instance ReferenceMeasure.prod [ReferenceMeasure α] [ReferenceMeasure β] :
    ReferenceMeasure (α × β) where
  toMeasurableSpace := inferInstance
  measure := ReferenceMeasure.measure.prod ReferenceMeasure.measure
  toSigmaFinite := inferInstance

/-- Counting measure as the state measure on Fin n → α when α is discrete/countable. -/
noncomputable instance {n : ℕ} {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] :
    ReferenceMeasure (Fin n → α) where
  toMeasurableSpace := inferInstance
  measure := (Measure.count : Measure (Fin n → α))
  toSigmaFinite := inferInstance


