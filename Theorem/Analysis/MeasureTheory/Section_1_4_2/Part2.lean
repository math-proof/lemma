module
public import Mathlib.SetTheory.Cardinal.Aleph
public import Instance.Analysis.MeasureTheory.Section_1_4_1.Part4
public import Def.Analysis.MeasureTheory.Section_1_4_2.Part2


public section

/-- Exercise 1.4.11 -/
theorem LebesgueMeasurable.boolean_algebra.isSigmaAlgebra (d:ℕ) : (LebesgueMeasurable.boolean_algebra d).isSigmaAlgebra :=
  fun E hE => LebesgueMeasurable.countable_union hE

