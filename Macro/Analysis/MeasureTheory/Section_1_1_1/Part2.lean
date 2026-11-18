module

public import Def.Analysis.MeasureTheory.Notation.Part2

public meta section


/-- Using ||ᵥ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

