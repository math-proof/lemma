import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Instance.Data.Holor.Tensor.Part2
import Def.LinearAlgebra.Matrix.Dense
open scoped Matrix


class PosDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  pd : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)


class NegDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  nd : PosDefAsymm (-A)


