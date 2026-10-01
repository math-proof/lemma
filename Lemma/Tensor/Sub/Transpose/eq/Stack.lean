import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {k : ℕ}
  {A : Matrix (Fin k) (Fin k) ℝ} :
-- imply
  A - Aᵀ = Matrix.of fun i j => A i j - A j i := by
-- proof
  ext i j
  simp [Matrix.transpose_apply]


-- created on 2023-05-24
