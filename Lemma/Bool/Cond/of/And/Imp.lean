import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : (p → q) ∧ p) :
-- imply
  q :=
-- proof
  h.1 h.2


-- created on 2026-09-26
