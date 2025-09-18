import Lemma.Set.In_Iic.is.Le
open Set


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Iic a ↔ a ≥ x := by
-- proof
  apply In_Iic.is.Le


-- created on 2025-04-27
-- updated on 2025-08-02
