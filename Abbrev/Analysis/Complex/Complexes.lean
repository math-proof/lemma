module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Instance.Analysis.Real.Numbers
public import Def.Analysis.Complex.Complexes

@[expose] public section


/-- Complex conjugate. This is `starRingEnd ℂ`, matching SymPy `~z`. -/
abbrev Complex.conj (z : ℂ) : ℂ := starRingEnd ℂ z

