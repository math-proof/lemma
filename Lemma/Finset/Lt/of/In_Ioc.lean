import Initialize.Tactic.Attr.Basic
import Theorem.Data.Set.Sets


@[path]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h : x ∈ Finset.Ioc a b) :
-- imply
  a < x := by
-- proof
  simp_all


-- created on 2025-12-30
