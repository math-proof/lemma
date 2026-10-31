import Def.Analysis.SpecialFunctions.TensorFunctions
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Defs


/-- py `SwapMatrix(n, i, j)`: the permutation matrix of the transposition `(i j)`.
Lean `Matrix` form (Fin indices; entries via `NatCast` from `KroneckerDelta`). Tensor
counterpart: `Def.LinearAlgebra.Matrix.Permutation.Tensor.SwapMatrix`. -/
def swapMatrix {α : Type*} [NatCast α] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) α :=
  Matrix.of fun a b => KroneckerDelta (Equiv.swap i j a) b
