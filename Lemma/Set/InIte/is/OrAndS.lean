import Lemma.Bool.BFn_Ite.is.OrAndS
open Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (S : Set α)
  (a b : α) :
-- imply
  (if p then
    a
  else
    b) ∈ S ↔ a ∈ S ∧ p ∨ b ∈ S ∧ ¬p := by
-- proof
  apply BFn_Ite.is.OrAndS


-- created on 2025-08-02
