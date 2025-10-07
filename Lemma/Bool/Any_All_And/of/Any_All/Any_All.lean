import sympy.Basic


@[main]
private lemma main
  {f : α → β → Prop}
  {g : α' → β' → Prop}
-- given
  (h₀ : ∃ M : β, ∀ x : α, f x M)
  (h₁ : ∃ N : β', ∀ y : α', g y N) :
-- imply
  ∃ N M, ∀ y : α', ∀ x : α, (f x M) ∧ (g y N) := by
-- proof
  cases h₀ with
  | intro M hM =>
    cases h₁ with
    | intro N hN =>
      -- Use the extracted M and N as witnesses
      exists N, M
      -- Prove the universal quantification part
      intro y x
      -- Combine the specialized hypotheses for y and x
      exact ⟨hM x, hN y⟩


-- created on 2025-07-19
