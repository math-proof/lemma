import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  ¬a > b :=
-- proof
  lt_asymm h


-- created on 2025-03-27
