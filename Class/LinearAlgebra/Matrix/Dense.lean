module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Instance.Data.Tensor.Tensor
public import Def.LinearAlgebra.Matrix.Dense
public section
open scoped Matrix


class PosDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  pd : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)


class NegDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  nd : PosDefAsymm (-A)


