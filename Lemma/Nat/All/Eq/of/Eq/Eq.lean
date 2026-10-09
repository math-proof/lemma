import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f g : ℕ → ℤ}
  {n : ℕ}
-- given
  (h₀ : ∀ k < n, f k = g k)
  (h₁ : f n = g n) :
-- imply
  ∀ k < n + 1, f k = g k := by
-- proof
  intro k hk
  by_cases hkn : k < n
  · exact h₀ k hkn
  · rw [show k = n by omega]
    exact h₁


-- created on 2019-03-23
