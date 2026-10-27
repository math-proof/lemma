import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Instance.Analysis.Real.Numbers
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

