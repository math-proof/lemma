import sympy.Basic


@[main]
private lemma main
  {p q r s : Prop}
-- given
  (h : (q ∨ p) ∧ (r ∨ p) ∧ (s ∨ p)) :
-- imply
  p ∨ q ∧ r ∧ s := by
-- proof
  tauto


-- created on 2026-10-03
