import sympy.Basic


@[main]
private lemma main
  {f : α → β → Prop}
  {g : α → β → Prop}
  {A B : Set α}
-- given
  (h₀ : ∃ M, ∀ x ∈ A, f x M)
  (h₁ : ∃ N, ∀ x ∈ B, g x N) :
-- imply
  ∃ M N, ∀ x ∈ A ∩ B, f x M ∧ g x N := by
-- proof
  cases h₀ with
  | intro M hM =>
    cases h₁ with
    | intro N hN =>
      exists M, N
      intro x hx
      exact ⟨hM x hx.left, hN x hx.right⟩


-- created on 2019-02-24
-- updated on 2026-09-21
