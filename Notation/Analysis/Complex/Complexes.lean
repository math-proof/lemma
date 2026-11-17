module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Instance.Analysis.Real.Numbers
public import Abbrev.Analysis.Complex.Complexes

public section


/-- Prefix `~z` for `Complex.conj z`. Binds as tightly as a max-precedence atom (`~ω ^ 2` is `(~ω) ^ 2`). -/
prefix:max "~" => Complex.conj

