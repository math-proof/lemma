import sympy.Basic


@[path]
private lemma symbol.domain_defined
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Set.Icc a b) :
-- imply
  a ≤ b :=
-- proof
  h.1.trans h.2


-- created on 2026-09-27
