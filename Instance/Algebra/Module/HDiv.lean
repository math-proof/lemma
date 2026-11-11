import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic


/-- Scalar division of a vector: `v / c = c⁻¹ • v`.
Low priority so `ℝ / ℝ` keeps the field instance. -/
noncomputable instance (priority := 100) {E : Type*} [AddCommGroup E] [Module ℝ E] :
    HDiv E ℝ E where
  hDiv v c := c⁻¹ • v
