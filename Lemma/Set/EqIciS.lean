import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α] [LocallyFiniteOrderTop α]
-- given
  (i : α) :
-- imply
  Ici i = Finset.Ici i := by
-- proof
  simp


-- created on 2025-05-18
