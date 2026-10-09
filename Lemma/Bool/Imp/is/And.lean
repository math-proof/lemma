import sympy.Basic


@[path]
private lemma main
  {p q r : Prop} :
-- imply
  (p → q ∧ r) ↔ (p → q) ∧ (p → r) :=
-- proof
  imp_and


-- created on 2019-10-07
