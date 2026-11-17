module

public section


public theorem Bool.Or.of.Or.Imp.left
-- given
  (h₀ : p → q)
  (h₁ : p ∨ r) :
-- imply
  q ∨ r := by
-- proof
  cases h₁ with
  | inr hr =>
    apply Or.inr
    exact hr
  | inl hp =>
    apply Or.inl
    exact h₀ hp


public theorem Bool.Or.of.Or.Imp
-- given
  (h₀ : p → q)
  (h₁ : r ∨ p) :
-- imply
  r ∨ q := by
-- proof
  cases h₁ with
  | inl hr =>
    apply Or.inl
    exact hr
  | inr hp =>
    apply Or.inr
    exact h₀ hp


-- created on 2026-11-17
