import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (i n : α) :
-- imply
  Ioc i n = Finset.Ioc i n := by
-- proof
  simp


-- created on 2025-05-18
