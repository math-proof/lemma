import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : (∃ x ∈ A, g x) ∨ ∃ x ∈ A, f x) :
-- imply
  ∃ x ∈ A, g x ∨ f x := by
-- proof
  rcases h with ⟨x, hx, hg⟩ | ⟨x, hx, hf⟩
  ·
    exact ⟨x, hx, Or.inl hg⟩
  ·
    exact ⟨x, hx, Or.inr hf⟩


-- created on 2026-09-27
