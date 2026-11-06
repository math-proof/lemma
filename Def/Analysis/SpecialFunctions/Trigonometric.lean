import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Instance.Analysis.Real.Numbers
import Class.Analysis.SpecialFunctions.Trigonometric
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

