module

public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

namespace Matrix

variable {m n : Type*} {α : Type*}

/-- Scale row `i` of a matrix by the `i`-th entry of a vector. No summation. -/
instance [Mul α] : SMul (m → α) (Matrix m n α) where
  smul v A := fun i j => v i * A i j

@[simp] theorem vec_smul_apply [Mul α] (v : m → α) (A : Matrix m n α) (i : m) (j : n) :
    (v • A) i j = v i * A i j :=
  rfl

end Matrix
