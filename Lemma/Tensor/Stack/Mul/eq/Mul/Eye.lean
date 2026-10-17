import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {h : Fin n → ℝ} :
-- imply
  ∀ i j, (if i = j then h i else 0) = (if i = j then (1 : ℝ) else 0) * h i := by
-- proof
  intro i j
  if hij : i = j then
    simp [hij]
  else
    simp [hij]


-- created on 2026-10-11
-- updated on 2026-10-17
