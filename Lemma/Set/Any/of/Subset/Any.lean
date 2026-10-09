import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
  {p : α → Prop}
-- given
  (h₀ : B ⊆ A)
  (h₁ : ∃ x ∈ B, p x) :
-- imply
  ∃ x ∈ A, p x := by
-- proof
  obtain ⟨x, hx, hp⟩ := h₁
  exact ⟨x, h₀ hx, hp⟩


-- created on 2019-07-10
