module

public import Def.Analysis.MeasureTheory.Notation.Part2

public meta section


/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

