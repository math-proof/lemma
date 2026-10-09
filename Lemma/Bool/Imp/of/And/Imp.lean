import sympy.Basic


@[path]
private lemma invert.given
  {p q c : Prop}
-- given
  (h₀ : p ∧ c → q)
  (h₁ : ¬p ∨ c) :
-- imply
  p → q := by
-- proof
  intro hp
  rcases h₁ with h | h
  ·
    exact absurd hp h
  ·
    exact h₀ ⟨hp, h⟩


-- created on 2023-10-03
