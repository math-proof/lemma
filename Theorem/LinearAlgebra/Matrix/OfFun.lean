module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Abbrev.LinearAlgebra.Matrix.OfFun

public section

@[simp] theorem Matrix.ofFun_apply (m n : ℕ) (f : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
    Matrix.ofFun m n f i j = f i j :=
  rfl

