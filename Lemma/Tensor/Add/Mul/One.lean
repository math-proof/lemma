import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {A : Matrix (Fin n) (Fin m) ℝ}
  {v : Fin m → ℝ} :
-- imply
  Matrix.of (fun i j => A i j + v j) = A + Matrix.of (fun _ j => v j) := by
-- proof
  ext i j
  simp


-- created on 2023-03-19
-- updated on 2026-10-26
