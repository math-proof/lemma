import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Instance.Analysis.Real.Numbers
import Class.Analysis.SpecialFunctions.Trigonometric
export Real (cos sin arccos arcsin tan cot)


noncomputable def Hyperreal.sin (x : ℝ*) : ℝ* :=
  x.map Real.sin

noncomputable def Hyperreal.cos (x : ℝ*) : ℝ* :=
  x.map Real.cos

noncomputable def Hyperreal.cot (x : ℝ*) : ℝ* :=
  x.map Real.cot

noncomputable def Hyperreal.tan (x : ℝ*) : ℝ* :=
  x.map Real.tan

