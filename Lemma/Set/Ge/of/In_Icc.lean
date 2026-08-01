import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  x ≥ a :=
-- proof
  h.left


-- created on 2018-04-05
-- updated on 2025-05-18
