import sympy.Basic


@[main]
private lemma induct
  {P : ℕ → Prop}
-- given
  (h₀ : P 1)
  (h₁ : P 2)
  (h₂ : ∀ n ≥ 1, P n ∧ P (n + 1) → P (n + 2)) :
-- imply
  ∀ n ≥ 1, P n := by
-- proof
  have key : ∀ m, P (m + 1) ∧ P (m + 2) := by
    intro m
    induction m with
    | zero =>
      exact ⟨h₀, h₁⟩
    | succ m ih =>
      exact ⟨ih.2, h₂ (m + 1) (by omega) ih⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1


-- created on 2026-09-27
