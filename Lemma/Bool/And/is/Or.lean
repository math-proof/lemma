import sympy.Basic


@[main]
private lemma collect :
-- imply
  (q ∨ p) ∧ (r ∨ p) ∧ (s ∨ p) ↔ p ∨ q ∧ r ∧ s := by
-- proof
  tauto


-- created on 2026-09-27
