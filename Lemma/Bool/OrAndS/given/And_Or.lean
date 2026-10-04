import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : (p ∧ r) ∨ (q ∧ r)) :
-- imply
  r ∧ (p ∨ q) := by
-- proof
  grind


-- created on 2020-02-18
