module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Def.Probability.Rv.Part2

public section

open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

attribute [simp] CountableMeasure.measure_eq_count

-- Bare `x ~ D` (density-form) removed: use `x ∼[π] μ` / `HasLaw x μ π` instead.
