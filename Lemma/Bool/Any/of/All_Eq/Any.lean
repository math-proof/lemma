import sympy.Basic


@[path]
private lemma subst
  {C : Set γ}
  {a : α}
  {f : γ → α}
  {p : α → γ → Prop}
-- given
  (h₀ : ∀ c ∈ C, a = f c)
  (h₁ : ∃ c ∈ C, p a c) :
-- imply
  ∃ c ∈ C, p (f c) c := by
-- proof
  obtain ⟨c, hc, hp⟩ := h₁
  exact ⟨c, hc, h₀ c hc ▸ hp⟩


-- created on 2019-01-06
