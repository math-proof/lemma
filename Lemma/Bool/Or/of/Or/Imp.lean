import sympy.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : p ∨ r) :
-- imply
  q ∨ r := by
-- proof
  -- Consider the two cases derived from the disjunction `r ∨ p`
  cases h₁ with
  | inr hr =>
    -- Case 1: `r` is true. Use ∨-intro to conclude `r ∨ q`.
    apply Or.inr
    exact hr
  | inl hp =>
    -- Case 2: `p` is true. Use modus ponens to derive `q`, then use ∨-intro to conclude `r ∨ q`.
    apply Or.inl
    exact h₀ hp


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r ∨ p) :
-- imply
  r ∨ q := by
-- proof
  -- Consider the two cases derived from the disjunction `r ∨ p`
  cases h₁ with
  | inl hr =>
    -- Case 1: `r` is true. Use ∨-intro to conclude `r ∨ q`.
    apply Or.inl
    exact hr
  | inr hp =>
    -- Case 2: `p` is true. Use modus ponens to derive `q`, then use ∨-intro to conclude `r ∨ q`.
    apply Or.inr
    exact h₀ hp


-- created on 2025-04-11
-- updated on 2025-04-12
