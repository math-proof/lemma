import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  x ≤ y := by
-- proof
  rw [h]


-- created on 2025-03-29
