module

public import Mathlib
public import Abbrev.Analysis.MeasureTheory.Section_1_1_1
@[expose] public section

open BoundedInterval


/-- Definition 1.1.1 (boxes): The length of an interval is max(b - a, 0). -/
abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0
