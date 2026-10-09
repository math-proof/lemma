import sympy.Basic


@[path]
private lemma main
  {f : ℕ → ℤ}
  {g : ℕ → ℤ}
-- given
  (h₀ : ∃ N, ∀ n ≥ N, f n ≤ g N)
  (h₁ : ∀ N, ∀ n < N, f n ≤ g N) :
-- imply
  ∃ N, ∀ n, f n ≤ g N := by
-- proof
  obtain ⟨N, hN⟩ := h₀
  refine ⟨N, fun n => ?_⟩
  by_cases hn : n < N
  ·
    exact h₁ N n hn
  ·
    exact hN n (Nat.le_of_not_lt hn)


-- created on 2019-02-23
