module

public import Theorem.Algebra.Power.Part2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Hyperreal
public import Class.Algebra.Polynomial.Polyroots

public section


notation:max (priority := 1001) "√" x:max => Root.sqrt x

notation:max "∛" x:max => Root.cubic x

notation:max "∜" x:max => Root.quartic x


