import sympy.Basic


@[main]
private lemma main
  {p q r c : Prop}
-- given
  (h : (p ∨ c) ∧ q ∧ (r ∨ c)) :
-- imply
  q ∧ (c ∨ p ∧ r) := by
-- proof
  tauto


-- created on 2026-10-03
