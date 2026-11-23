module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Instance.Analysis.Real.Numbers
public import Class.Analysis.SpecialFunctions.Trigonometric

@[expose] public section

export Real (cos sin arccos arcsin tan cot arctan)


noncomputable def Hyperreal.sin (x : ℝ*) : ℝ* :=
  x.map Real.sin

noncomputable def Hyperreal.cos (x : ℝ*) : ℝ* :=
  x.map Real.cos

noncomputable def Hyperreal.cot (x : ℝ*) : ℝ* :=
  x.map Real.cot

noncomputable def Hyperreal.tan (x : ℝ*) : ℝ* :=
  x.map Real.tan

noncomputable def Hyperreal.arctan (x : ℝ*) : ℝ* :=
  x.map Real.arctan

