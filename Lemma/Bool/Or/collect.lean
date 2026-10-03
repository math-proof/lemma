import sympy.Basic


@[main]
private lemma main
  {p q r c : Prop}
-- given
  (h : p ∨ (q ∧ c) ∨ (r ∧ c)) :
-- imply
  p ∨ ((q ∨ r) ∧ c) := by
-- proof
  tauto


-- created on 2026-10-03
