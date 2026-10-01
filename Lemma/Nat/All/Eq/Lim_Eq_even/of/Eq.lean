import sympy.Basic


@[main]
private lemma main
  {f g : ℤ → ℝ}
-- given
  (h : ∀ n, f (2 * n) = g (2 * n)) :
-- imply
  ∀ n, n % 2 = 0 → f n = g n := by
-- proof
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  exact h k


-- created on 2019-03-28
