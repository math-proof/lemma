import sympy.Basic


@[main]
private lemma main
  {p q r : Prop} :
-- imply
  (p → q ∧ r) ↔ (p → q) ∧ (p → r) :=
-- proof
  imp_and


-- created on 2026-09-27
