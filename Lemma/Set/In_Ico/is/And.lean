import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x a b : α} :
-- imply
  x ∈ Ico a b ↔ x ≥ a ∧ x < b :=
-- proof
  Iff.rfl


-- created on 2020-03-24
