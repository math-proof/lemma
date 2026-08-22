import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import sympy.core.numbers

noncomputable def Complex.sign (z : ℂ) : ℂ := z / ‖z‖

/-- Complex conjugate. This is `starRingEnd ℂ`, matching SymPy `~z`. -/
abbrev Complex.conj (z : ℂ) : ℂ := starRingEnd ℂ z

/-- Prefix `~z` for `Complex.conj z`. Binds as tightly as a max-precedence atom (`~ω ^ 2` is `(~ω) ^ 2`). -/
prefix:max "~" => Complex.conj

export Complex (re im arg sign conj)
