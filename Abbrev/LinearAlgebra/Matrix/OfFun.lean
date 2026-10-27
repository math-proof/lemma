import Mathlib.LinearAlgebra.Matrix.Defs


/-- Fin-indexed matrix from an entry function (sugar target for `[i < m, j < n]`). -/
abbrev Matrix.ofFun (m n : ℕ) (f : Fin m → Fin n → α) : Matrix (Fin m) (Fin n) α :=
  Matrix.of f

