import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioo a b) :
-- imply
  x > a :=
-- proof
  h₀.left


-- created on 2025-03-01
-- updated on 2025-05-18
