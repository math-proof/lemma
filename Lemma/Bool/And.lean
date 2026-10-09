import sympy.Basic


@[path]
private lemma collect :
-- imply
  (a ∨ c) ∧ f ∧ (x ∨ c) ↔ f ∧ (c ∨ a ∧ x) := by
-- proof
  tauto


@[path]
private lemma distribute :
-- imply
  (p ∨ q) ∧ r ∧ s ↔ (p ∧ r ∨ q ∧ r) ∧ s := by
-- proof
  tauto


@[path]
private lemma invert
-- given
  (h : p ∧ q) :
-- imply
  (p ∨ ¬q) ∧ q := by
-- proof
  tauto


-- created on 2019-04-30
