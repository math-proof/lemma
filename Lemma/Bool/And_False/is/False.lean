import sympy.Basic


@[main]
private lemma main :
-- imply
  p ∧ False ↔ False := by
-- proof
  apply Iff.intro
  intro h
  exact h.right
  intro hf
  exact hf.elim


-- created on 2024-07-01
