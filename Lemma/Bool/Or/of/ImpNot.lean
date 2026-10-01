import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  ¬p ∨ q := by
-- proof
  grind


-- created on 2026-10-01
