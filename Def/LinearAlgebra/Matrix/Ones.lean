import Mathlib.Data.Matrix.Basic


/-- The matrix with every entry equal to `1`. -/
def Matrix.ones (m n : Type*) (α : Type*) [One α] : Matrix m n α :=
  Matrix.of fun _ _ => 1
