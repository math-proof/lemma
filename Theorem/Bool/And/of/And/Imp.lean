module

public section


public theorem Bool.And.of.And.Imp.left
-- given
  (h₀ : p → q)
  (h₁ : p ∧ r) :
-- imply
  q ∧ r := by
-- proof
  let ⟨hp, hr⟩ := h₁
  have hq := h₀ hp
  exact ⟨hq, hr⟩


public theorem Bool.And.of.And.Imp
-- given
  (h₀ : p → q)
  (h₁ : r ∧ p) :
-- imply
  r ∧ q := by
-- proof
  let ⟨hr, hp⟩ := h₁
  have hq := h₀ hp
  exact ⟨hr, hq⟩


-- created on 2026-11-17
