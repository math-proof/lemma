import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


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


-- created on 2019-10-17
-- updated on 2026-10-26
