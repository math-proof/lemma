module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Instance.Analysis.Real.Numbers

@[expose] public section


noncomputable def Complex.sign (z : ℂ) : ℂ := z / ‖z‖

