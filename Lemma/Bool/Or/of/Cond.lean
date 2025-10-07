import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p) :
-- imply
  p ∨ q :=
-- proof
  Or.inl h


-- created on 2025-04-05
