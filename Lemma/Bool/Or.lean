import sympy.Basic


@[path]
private lemma collect
-- given
  (h : p ∨ q ∧ c ∨ r ∧ c) :
-- imply
  p ∨ (q ∨ r) ∧ c := by
-- proof
  tauto


@[path]
private lemma invert
-- given
  (h : p ∨ q) :
-- imply
  p ∧ ¬q ∨ q := by
-- proof
  tauto


-- created on 2020-02-16
