import Lemma.Matrix.SetOfDotGetSwapMatrix.eq.Range
open Matrix


@[path]
private lemma main
  [Semiring α]
  {s : Set α}
  {P : Set (Fin n → α)}
  {i j : Fin n}
-- given
  (hP : P = {x | Set.range x = s}) :
-- imply
  ∀ x ∈ P, swapMatrix (α := α) i j *ᵥ x ∈ P := by
-- proof
  intro x hx
  rw [hP] at hx ⊢
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [SetOfDotGetSwapMatrix.eq.Range]
  apply hx


-- created on 2026-10-31
