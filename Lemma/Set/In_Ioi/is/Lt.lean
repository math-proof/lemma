import sympy.sets.sets
import Lemma.Set.In_Ioi.is.Gt
open Set


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Ioi a ↔ a < x := by
-- proof
  apply In_Ioi.is.Gt


-- created on 2025-04-27
-- updated on 2025-08-02
