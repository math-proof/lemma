import Lemma.Set.In_Ioi.is.Lt
open Set


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Ioi a ↔ x > a := by
-- proof
  apply In_Ioi.is.Lt


-- created on 2025-04-27
-- updated on 2026-08-19
