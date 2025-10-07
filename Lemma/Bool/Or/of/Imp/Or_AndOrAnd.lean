import sympy.core.logic
import sympy.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : r₀ ∨ ((p ∧ r₁) ∨ r₂) ∧ r₃) :
-- imply
  r₀ ∨ ((q ∧ r₁) ∨ r₂) ∧ r₃ := by
-- proof
  mpr [h₀]
  assumption


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r₀ ∨ (r₁ ∧ p ∨ r₂) ∧ r₃) :
-- imply
  r₀ ∨ (r₁ ∧ q ∨ r₂) ∧ r₃ := by
-- proof
  mp [h₀] at h₁
  exact h₁


-- created on 2025-04-12
