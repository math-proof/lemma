import Initialize.Tactic.Attr.Basic
import Theorem.Data.Set.Sets


@[path]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h₀ : x ∈ Finset.Ico a b) :
-- imply
  a ≤ x := by
-- proof
  simp_all


-- created on 2025-12-30
