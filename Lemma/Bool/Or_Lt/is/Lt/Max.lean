import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x a b : α} :
-- imply
  x < a ∨ x < b ↔ x < max a b :=
-- proof
  lt_max_iff.symm


-- created on 2022-01-02
