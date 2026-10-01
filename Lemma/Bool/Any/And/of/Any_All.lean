import sympy.Basic


@[main]
private lemma subst
  {A : Set α}
  {f : α → γ → Prop}
  {x₀ : α}
-- given
  (h₀ : x₀ ∈ A)
  (h₁ : ∃ C, ∀ x ∈ A, f x C) :
-- imply
  ∃ C, ∀ x ∈ A, f x₀ C ∧ f x C := by
-- proof
  obtain ⟨C, hC⟩ := h₁
  exact ⟨C, fun x hx => ⟨hC x₀ h₀, hC x hx⟩⟩


-- created on 2026-09-27
