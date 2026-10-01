import sympy.Basic


@[main]
private lemma collect
-- given
  (h : p ∨ q ∧ r ∧ s) :
-- imply
  (q ∨ p) ∧ (r ∨ p) ∧ (s ∨ p) := by
-- proof
  tauto


-- created on 2026-09-27
