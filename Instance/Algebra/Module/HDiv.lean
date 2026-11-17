module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-- Scalar division of a vector: `v / c = c⁻¹ • v`.
Low priority so `ℝ / ℝ` keeps the field instance. -/
noncomputable instance (priority := 100) {E : Type*} [AddCommGroup E] [Module ℝ E] :
    HDiv E ℝ E where
  hDiv v c := c⁻¹ • v
