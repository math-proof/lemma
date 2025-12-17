import sympy.sets.sets
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (a b : α) :
-- imply
  x ∈ Ioc a b ↔ a < x ∧ x ≤ b := by
-- proof
  rfl


-- created on 2025-03-02
