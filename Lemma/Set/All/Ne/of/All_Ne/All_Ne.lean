import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℤ}
-- given
  (h₀ : ∀ i < n, ∀ j < i, x i ≠ x j)
  (h₁ : ∀ i < n, x n ≠ x i) :
-- imply
  ∀ i < n + 1, ∀ j < i, x i ≠ x j := by
-- proof
  intro i hi j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · exact h₀ i h j hj
  · subst h
    exact h₁ j hj


-- created on 2026-09-27
