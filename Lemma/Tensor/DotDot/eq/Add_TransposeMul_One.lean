import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {Q K : Matrix (Fin n) (Fin n) ℝ}
  {b c : Fin n → ℝ}
  {d : ℝ} :
-- imply
  Matrix.of (fun i j => dotProduct (Q i) (K j) + b i + c j + d) =
    Matrix.of (fun i j => dotProduct (Q i) (K j)) +
      Matrix.of (fun i _ => b i) + Matrix.of (fun _ j => c j) + Matrix.of (fun _ _ => d) := by
-- proof
  ext i j
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
