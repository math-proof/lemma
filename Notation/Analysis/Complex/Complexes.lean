import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Instance.Analysis.Real.Numbers
import Abbrev.Analysis.Complex.Complexes


/-- Prefix `~z` for `Complex.conj z`. Binds as tightly as a max-precedence atom (`~ω ^ 2` is `(~ω) ^ 2`). -/
prefix:max "~" => Complex.conj

