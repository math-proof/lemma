import sympy.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a ≠ b ↔ False := by
-- proof
  constructor
  intro h₀
  exact h₀ h
  intro h₁
  exfalso
  exact h₁


-- created on 2025-03-29
