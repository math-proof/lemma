import Lemma.Logic.BFnIte.is.OrAndS
open Logic


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (x : α)
  (A B : Set α) :
-- imply
  x ∈ (if p then
    A
  else
    B) ↔ x ∈ A ∧ p ∨ x ∈ B ∧ ¬p := by
-- proof
  apply BFnIte.is.OrAndS


-- created on 2025-08-02
