import sympy.core.logic
import sympy.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : r' ∨ (p ∨ r) ∧ r'') :
-- imply
  r' ∨ (q ∨ r) ∧ r'' := by
-- proof
  mpr [h₀]
  assumption


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r' ∨ (r ∨ p) ∧ r'') :
-- imply
  r' ∨ (r ∨ q) ∧ r'' := by
-- proof
  mp [h₀] at h₁
  assumption


-- created on 2025-04-12
