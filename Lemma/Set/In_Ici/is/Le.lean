import Lemma.Set.In_Ici.is.Ge
open Set


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Ici a ↔ a ≤ x := by
-- proof
  apply In_Ici.is.Ge


-- created on 2025-04-27
-- updated on 2025-08-02
