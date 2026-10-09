import sympy.Basic


@[path]
private lemma trans'
  {a b c : α}
-- given
  (h : a = b ∧ a = c) :
-- imply
  a = b ∧ b = c :=
-- proof
  ⟨h.1, h.1.symm.trans h.2⟩


@[path]
private lemma collect.given
-- given
  (h : f ∧ (c ∨ a ∧ x)) :
-- imply
  (a ∨ c) ∧ f ∧ (x ∨ c) := by
-- proof
  tauto


@[path]
private lemma collect
-- given
  (h : (a ∨ c) ∧ f ∧ (x ∨ c)) :
-- imply
  f ∧ (c ∨ a ∧ x) := by
-- proof
  tauto


@[path]
private lemma delete
-- given
  (h : p ∧ q ∧ r) :
-- imply
  p ∧ (q ∧ r) :=
-- proof
  h


-- created on 2019-04-29
