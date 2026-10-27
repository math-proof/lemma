import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Instance.Analysis.Real.Numbers
import Def.Analysis.SpecialFunctions.Trigonometric
export Real (cos sin arccos arcsin tan cot)


noncomputable instance : Sin ℝ where
  sin := Real.sin

noncomputable instance : Cos ℝ where
  cos := Real.cos

noncomputable instance : Cot ℝ where
  cot := Real.cot

noncomputable instance : Tan ℝ where
  tan := Real.tan

noncomputable instance : Sin ℂ where
  sin := Complex.sin

noncomputable instance : Cos ℂ where
  cos := Complex.cos

noncomputable instance : Cot ℂ where
  cot := Complex.cot

noncomputable instance : Tan ℂ where
  tan := Complex.tan

noncomputable instance : Sin ℝ* where
  sin := Hyperreal.sin

noncomputable instance : Cos ℝ* where
  cos := Hyperreal.cos

noncomputable instance : Cot ℝ* where
  cot := Hyperreal.cot

noncomputable instance : Tan ℝ* where
  tan := Hyperreal.tan


