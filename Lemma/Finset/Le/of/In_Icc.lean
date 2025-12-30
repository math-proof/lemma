import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h : x ∈ Finset.Icc a b) :
-- imply
  x ≤ b := by
-- proof
  simp_all


-- created on 2025-12-30
