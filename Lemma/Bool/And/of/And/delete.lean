import sympy.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∧ q ∧ r) :
-- imply
  q ∧ r :=
-- proof
  h.2


-- created on 2019-05-05
