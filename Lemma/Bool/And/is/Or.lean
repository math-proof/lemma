import sympy.Basic


@[path]
private lemma collect :
-- imply
  (q ∨ p) ∧ (r ∨ p) ∧ (s ∨ p) ↔ p ∨ q ∧ r ∧ s := by
-- proof
  tauto


-- created on 2022-01-28
