import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : p → r) :
-- imply
  p → q ∧ r := by
-- proof
    -- Assume p to prove q ∧ r
  intro h
    -- Derive q using h₀ and the assumption h
  have q := h₀ h
    -- Derive r using h₁ and the assumption h
  have r := h₁ h
    -- Combine q and r into q ∧ r
  exact ⟨q, r⟩


-- created on 2025-04-10
