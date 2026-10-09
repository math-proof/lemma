import sympy.Basic


@[path]
private lemma induct
  {f g : ℕ → ℤ}
-- given
  (h₀ : f 1 = g 1)
  (h₁ : f 2 = g 2)
  (h₂ : ∀ n ≥ 1, f n = g n → f (n + 2) = g (n + 2)) :
-- imply
  ∀ n ≥ 1, f n = g n := by
-- proof
  have key : ∀ m, f (m + 1) = g (m + 1) ∧ f (m + 2) = g (m + 2) := by
    intro m
    induction m with
    | zero =>
      exact ⟨h₀, h₁⟩
    | succ m ih =>
      exact ⟨ih.2, h₂ (m + 1) (by omega) ih.1⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1


-- created on 2019-03-28
