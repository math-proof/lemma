import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import sympy.core.numbers

export Real (cos sin arccos arcsin tan cot)

/--
Sine on a type that carries `sin`. Instances for `ℝ`, `ℂ`, and `ℝ*`.
-/
class Sin (α : Type*) where
  sin : α → α

/--
Cosine on a type that carries `cos`. Instances for `ℝ`, `ℂ`, and `ℝ*`.
-/
class Cos (α : Type*) where
  cos : α → α

/--
Cotangent on a type that carries `cot`. Instances for `ℝ`, `ℂ`, and `ℝ*`.
-/
class Cot (α : Type*) where
  cot : α → α

/--
Tangent on a type that carries `tan`. Instances for `ℝ`, `ℂ`, and `ℝ*`.
-/
class Tan (α : Type*) where
  tan : α → α

noncomputable def Hyperreal.sin (x : ℝ*) : ℝ* :=
  x.map Real.sin

noncomputable def Hyperreal.cos (x : ℝ*) : ℝ* :=
  x.map Real.cos

noncomputable def Hyperreal.cot (x : ℝ*) : ℝ* :=
  x.map Real.cot

noncomputable def Hyperreal.tan (x : ℝ*) : ℝ* :=
  x.map Real.tan

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
