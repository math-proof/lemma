import sympy.core.logic
import sympy.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : r₀ ∨ ((r₁ ∧ (p ∨ r₃)) ∨ r₄) ∧ r₅) :
-- imply
  r₀ ∨ ((r₁ ∧ (q ∨ r₃)) ∨ r₄) ∧ r₅ := by
-- proof
  mpr [h₀]
  assumption


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r₀ ∨ ((r₁ ∧ (r₃ ∨ p)) ∨ r₄) ∧ r₅) :
-- imply
  r₀ ∨ ((r₁ ∧ (r₃ ∨ q)) ∨ r₄) ∧ r₅ := by
-- proof
  mp [h₀] at h₁
  assumption


-- created on 2025-04-12
-- updated on 2025-04-13
