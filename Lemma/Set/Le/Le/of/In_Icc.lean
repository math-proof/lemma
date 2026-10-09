import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  a ≤ x ∧ x ≤ b :=
-- proof
  ⟨h.left, h.right⟩


-- created on 2026-10-03
