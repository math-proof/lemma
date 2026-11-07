import Mathlib.LinearAlgebra.Matrix.Defs


namespace Matrix

variable {m n : Type*} {α : Type*}

/-- Entrywise division of a matrix by a scalar. -/
instance [Div α] : HDiv (Matrix m n α) α (Matrix m n α) where
  hDiv A c := fun i j => A i j / c

@[simp] theorem div_apply [Div α] (A : Matrix m n α) (c : α) (i : m) (j : n) :
    (A / c) i j = A i j / c :=
  rfl

/-- Entrywise multiplication of a matrix by a scalar on the right. -/
instance [Mul α] : HMul (Matrix m n α) α (Matrix m n α) where
  hMul A c := fun i j => A i j * c

@[simp] theorem mul_scalar_apply [Mul α] (A : Matrix m n α) (c : α) (i : m) (j : n) :
    (A * c) i j = A i j * c :=
  rfl

/-- Entrywise subtraction of a scalar from a matrix.
`@[default_instance high]` keeps a numeral on the right as that scalar, so `A - 1`
subtracts `(1 : α)` from every entry. It does not subtract the identity matrix. -/
@[default_instance high]
instance [Sub α] : HSub (Matrix m n α) α (Matrix m n α) where
  hSub A c := fun i j => A i j - c

@[simp] theorem sub_scalar_apply [Sub α] (A : Matrix m n α) (c : α) (i : m) (j : n) :
    (A - c) i j = A i j - c :=
  rfl

end Matrix
