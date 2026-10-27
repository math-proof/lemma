import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Instance.Analysis.Real.Numbers
import Def.Analysis.Complex.Complexes


/-- Complex conjugate. This is `starRingEnd ℂ`, matching SymPy `~z`. -/
abbrev Complex.conj (z : ℂ) : ℂ := starRingEnd ℂ z

