import sympy.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (h : (p ∧ r) ∨ q) :
-- imply
  (p ∨ q) ∧ (r ∨ q) := by
-- proof
  grind


-- created on 2026-10-03
