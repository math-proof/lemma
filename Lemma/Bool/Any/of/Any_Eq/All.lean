import sympy.Basic


@[main]
private lemma subst
  {S : Set γ}
  {f g : γ → α}
  {p : α → Prop}
-- given
  (h₀ : ∃ x ∈ S, g x = f x)
  (h₁ : ∀ x ∈ S, p (g x)) :
-- imply
  ∃ x ∈ S, p (f x) := by
-- proof
  obtain ⟨x, hx, he⟩ := h₀
  exact ⟨x, hx, he ▸ h₁ x hx⟩


-- created on 2019-02-25
