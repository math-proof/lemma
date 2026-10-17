import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n l : ℕ}
  {V Vq : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : ∀ i j, V i j = Vq i j) :
-- imply
  ∀ i : Fin n, ∀ j : Fin n, j.1 < min (i.1 + 1) l → V i j = Vq i j := by
-- proof
  intro i j _
  exact h₀ i j


-- created on 2026-10-11
-- updated on 2026-10-17
