import Lemma.Bool.BFn_Ite__Ite.is.And.ou.OrAndS
open Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (S : Set α)
  (a b c : α) :
-- imply
  (if p then
    a
  else if q then
    b
  else
    c) ∈ S ↔ (a ∈ S ∧ p) ∨ (b ∈ S ∧ q ∧ ¬p) ∨ (c ∈ S ∧ ¬(p ∨ q)) := by
-- proof
  apply BFn_Ite__Ite.is.And.ou.OrAndS


-- created on 2025-04-18
