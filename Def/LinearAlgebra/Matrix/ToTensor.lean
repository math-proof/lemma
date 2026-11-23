module

public import Mathlib.Data.Matrix.Basic
public import Def.Data.Tensor.Stack.Part2
public import Def.Data.Tensor.Tensor.Part2
public import Def.Data.Tensor.Item
public import Instance.Data.Tensor.Defs.Part3

@[expose] public section

/-- Rank-2 tensor whose entries are the matrix entries, row by row. -/
def Matrix.toTensor {m n : ℕ} {α : Type*} (A : Matrix (Fin m) (Fin n) α) : Tensor α [m, n] :=
  [i < m] [j < n] (A i j)


/-- Matrix of the entries of a rank-2 tensor. -/
def Tensor.toMatrixElem {m n : ℕ} {α : Type*} (X : Tensor α [m, n]) : Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => (X[i, j]).item
