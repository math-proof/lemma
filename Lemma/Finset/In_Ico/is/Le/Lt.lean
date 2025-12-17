import sympy.Basic
import sympy.sets.sets


@[main, comm, mp, mpr]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (a b : α) :
-- imply
  x ∈ Finset.Ico a b ↔ a ≤ x ∧ x < b := by
-- proof
  simp_all


-- created on 2025-12-16
