import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Ioi a ↔ a < x :=
-- proof
  UpperSet.mem_Ioi_iff


-- created on 2025-04-27
-- updated on 2026-10-26
