import Mathlib.Data.Matrix.Basic
import Def.Data.Holor.Stack.Part2
import Def.Data.Holor.Tensor.Part2
import Def.Data.Holor.Item
import Instance.Data.Holor.Defs.Part3


/-- Rank-2 tensor whose entries are the matrix entries, row by row. -/
def Matrix.toTensor {m n : ℕ} {α : Type*} (A : Matrix (Fin m) (Fin n) α) : Tensor α [m, n] :=
  [i < m] [j < n] (A i j)


/-- Matrix of the entries of a rank-2 tensor. -/
def Tensor.toMatrixElem {m n : ℕ} {α : Type*} (X : Tensor α [m, n]) : Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => (X[i, j]).item
