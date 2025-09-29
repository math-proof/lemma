import sympy.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : ¬a ≠ b) :
-- imply
  a = b := by
-- proof
  -- Use classical reasoning to handle the double negation
  by_contra h₀
    -- Apply the hypothesis `h` to the assumption `h₀ : a ≠ b` to derive a contradiction
  exact h h₀


-- created on 2025-03-30
