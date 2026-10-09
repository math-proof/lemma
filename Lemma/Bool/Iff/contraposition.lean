import sympy.Basic


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : p ↔ q) :
-- imply
  ¬q ↔ ¬p :=
-- proof
  not_congr h.symm


-- created on 2022-01-27
