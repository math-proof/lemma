import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  p → q :=
-- proof
  h.mp


-- created on 2018-01-25
