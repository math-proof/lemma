module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Basic.ENNReal.Real
public import Abbrev.Analysis.Real.Numbers

public section

export Complex (I)


notation "∞" => Hyperreal.omega

notation "ℝ⁺" => { x : ℝ // 0 < x }

notation "ℝ⁻" => { x : ℝ // x < 0 }
