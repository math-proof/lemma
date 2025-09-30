import sympy.sets.sets
import sympy.Basic


@[main, comm]
private lemma main
  [Preorder α]
-- given
  (a b : α)
  (f : α → Set β) :
-- imply
  ⋃ k ∈ Ico a b, f k = ⋃ k, ⋃ (_ : a ≤ k ∧ k < b), f k := by
-- proof
  simp


-- created on 2025-09-30
