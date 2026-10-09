import sympy.Basic


@[path]
private lemma main
  {f g : ℤ → ℝ}
-- given
  (h : ∀ n, f (2 * n + 1) = g (2 * n + 1)) :
-- imply
  ∀ n, n % 2 ≠ 0 → f n = g n := by
-- proof
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  exact h k


-- created on 2019-03-27
