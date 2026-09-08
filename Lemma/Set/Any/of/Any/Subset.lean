import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {p : α → Prop}
-- given
  (h₀ : A ⊆ B)
  (h₁ : ∃ e ∈ A, p e) :
-- imply
  ∃ e ∈ B, p e := by
-- proof
  obtain ⟨e, hA, hp⟩ := h₁
  exact ⟨e, h₀ hA, hp⟩


-- created on 2020-09-01
-- updated on 2026-09-08
