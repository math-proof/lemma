import Mathlib.LinearAlgebra.Matrix.Notation
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : A.conjTranspose = A) :
-- imply
  ∀ i, starRingEnd ℂ (A i i) = A i i := by
-- proof
  intro i
  have h := congr_fun (congr_fun h₀ i) i
  simpa [Matrix.conjTranspose_apply, starRingEnd_self_apply] using h


-- created on 2026-10-11
-- updated on 2026-10-17
