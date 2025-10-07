import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  p → q :=
-- proof
  h.mp


-- created on 2025-04-12
