import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  p ∨ q ↔ q := by
-- proof
  tauto


-- created on 2026-08-06
