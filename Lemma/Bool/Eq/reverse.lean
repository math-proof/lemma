import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ↔ q) :
-- imply
  q ↔ p :=
-- proof
  h.symm


-- created on 2019-04-19
