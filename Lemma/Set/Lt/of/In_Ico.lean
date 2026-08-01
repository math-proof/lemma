import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b) :
-- imply
  x < b :=
-- proof
  h₀.right


-- created on 2021-03-12
-- updated on 2025-05-18
