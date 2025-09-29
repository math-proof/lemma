import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  ¬a < b := by
-- proof
  rw [h]
  exact fun hgt => lt_irrefl b hgt


-- created on 2025-04-06
