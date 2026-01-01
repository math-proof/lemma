import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y :=
-- proof
  ne_of_lt h


-- created on 2024-07-01
-- updated on 2025-04-04
