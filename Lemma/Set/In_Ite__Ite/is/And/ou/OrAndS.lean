import Lemma.Bool.BFnIte__Ite.is.And.ou.OrAndS
open Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (x : α)
  (A B C : Set α) :
-- imply
  x ∈ (if p then
    A
  else if q then
    B
  else
    C) ↔ (x ∈ A ∧ p) ∨ (x ∈ B ∧ q ∧ ¬p) ∨ (x ∈ C ∧ ¬(p ∨ q)) := by
-- proof
  apply BFnIte__Ite.is.And.ou.OrAndS


-- created on 2025-08-02
