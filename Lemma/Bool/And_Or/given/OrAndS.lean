import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : q ∧ p ∨ r ∧ p) :
-- imply
  p ∧ (q ∨ r) := by
-- proof
  grind


-- created on 2026-10-03
