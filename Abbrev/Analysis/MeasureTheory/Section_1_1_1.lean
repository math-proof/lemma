module

public import Mathlib
public import Inductive.Analysis.MeasureTheory.Section_1_1_1
@[expose] public section

open BoundedInterval


/-- Extracts the left endpoint of a bounded interval. -/
abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

/-- Extracts the right endpoint of a bounded interval. -/
abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b
