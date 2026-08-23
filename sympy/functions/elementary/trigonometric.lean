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

noncomputable def Hyperreal.sin (x : ℝ*) : ℝ* :=
  x.map Real.sin

noncomputable def Hyperreal.cos (x : ℝ*) : ℝ* :=
  x.map Real.cos

noncomputable instance : Sin ℝ where
  sin := Real.sin

noncomputable instance : Cos ℝ where
  cos := Real.cos

noncomputable instance : Sin ℂ where
  sin := Complex.sin

noncomputable instance : Cos ℂ where
  cos := Complex.cos

noncomputable instance : Sin ℝ* where
  sin := Hyperreal.sin

noncomputable instance : Cos ℝ* where
  cos := Hyperreal.cos
