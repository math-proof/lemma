import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import sympy.core.numbers

noncomputable def Complex.sign (z : ℂ) : ℂ := z / ‖z‖

export Complex (re im arg sign)
