import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n r : ℕ}
  {W : Matrix (Fin n) (Fin n) ℝ}
  {A : Matrix (Fin n) (Fin r) ℝ}
  {B : Matrix (Fin r) (Fin n) ℝ}
  {x : Fin n → ℝ} :
-- imply
  (W + A * B).mulVec x = W.mulVec x + (A * B).mulVec x := by
-- proof
  simp [Matrix.add_mulVec]


-- created on 2026-10-11
-- updated on 2026-10-17
