import sympy.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  a = b ↔ False := by
-- proof
  constructor
    -- Forward direction: a = b → False
  intro h₀
  exact h h₀
    -- Reverse direction: False → a = b
  intro h₁
  exfalso
  exact h₁


-- created on 2025-03-29
